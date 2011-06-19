{-# OPTIONS_GHC -fno-warn-unused-matches -fno-warn-unused-binds -fno-warn-unused-imports #-}
module CoqPass ( coqPassCoreToString, coqPassCoreToCore )
where
import qualified Unique
import qualified Kind
import qualified UniqSupply
import qualified MkCore
import qualified TysWiredIn
import qualified TysPrim
import qualified Outputable
import qualified PrelNames
import qualified OccName
import qualified Name
import qualified Literal
import qualified Type
import qualified TypeRep
import qualified DataCon
import qualified DsMonad
import qualified IOEnv
import qualified TcRnTypes
import qualified TyCon
import qualified Coercion
import qualified Var
import qualified Id
import qualified Pair
import qualified FastString
import qualified BasicTypes
import qualified DataCon
import qualified CoreSyn
import qualified CoreUtils
import qualified Class
import qualified Data.Char 
import qualified Data.List
import qualified Data.Ord
import qualified Data.Typeable
import Data.Bits ((.&.), shiftL, (.|.))
import Prelude ( (++), (+), (==), Show, show, (.), ($) )
import qualified Prelude
import qualified HscTypes
import qualified GHC.Base
import qualified CoreMonad
import qualified System.IO.Unsafe

getTyConTyVars :: TyCon.TyCon -> [Var.TyVar]
getTyConTyVars tc =
  if TyCon.isFunTyCon tc
  then []
  else if TyCon.isPrimTyCon tc
       then []
       else TyCon.tyConTyVars tc

cmpAlts :: (CoreSyn.AltCon,[Var.Var],CoreSyn.Expr Var.Var) -> (CoreSyn.AltCon,[Var.Var],CoreSyn.Expr Var.Var) -> Data.Ord.Ordering
cmpAlts (CoreSyn.DEFAULT,_,_) _   = Data.Ord.LT
cmpAlts _ (CoreSyn.DEFAULT,_,_)   = Data.Ord.GT
cmpAlts (a1,_,_) (a2,_,_)         = Data.Ord.compare a2 a1

sortAlts :: [(CoreSyn.AltCon,[Var.Var],CoreSyn.Expr Var.Var)] -> [(CoreSyn.AltCon,[Var.Var],CoreSyn.Expr Var.Var)]
sortAlts x = Data.List.sortBy (\a b -> if a `CoreSyn.ltAlt` b then Data.Ord.LT else Data.Ord.GT) x

coreVarToWeakVar :: Var.Var -> CoreVarToWeakVarResult
coreVarToWeakVar v | Id.isId     v = CVTWVR_EVar  (Var.varType v)
coreVarToWeakVar v | Var.isTyVar v = CVTWVR_TyVar (coreKindToKind (Var.varType v))
coreVarToWeakVar v | Coercion.isCoVar v = CVTWVR_CoVar (Prelude.fst (Coercion.coVarKind v)) (Prelude.snd (Coercion.coVarKind v))
coreVarToWeakVar _                 = Prelude.error "Var.Var that is neither an expression, type variable, nor coercion variable!"

rawTyFunKind :: TyCon.TyCon -> ( [Kind] , Kind )
rawTyFunKind tc = ((Prelude.map coreKindToKind (Prelude.take (TyCon.tyConArity tc) argk))
                  ,
                   coreKindToKind (Coercion.mkArrowKinds (Prelude.drop (TyCon.tyConArity tc) argk) retk))
                   where (argk,retk) = Coercion.splitKindFunTys (TyCon.tyConKind tc)

tyConOrTyFun :: TyCon.TyCon -> Prelude.Either TyCon.TyCon TyCon.TyCon
tyConOrTyFun n =
   if n == TysPrim.statePrimTyCon     -- special-purpose hack treat State# as a type family since it has kind *->* but no tyvars
   then Prelude.Right n
   else if TyCon.isFamInstTyCon n
        then Prelude.Right n
        else if TyCon.isSynTyCon n
             then Prelude.Right n
             else Prelude.Left n

nat2int :: Nat -> Prelude.Int
nat2int O     = 0
nat2int (S x) = 1 + (nat2int x)

natToString :: Nat -> Prelude.String
natToString n = show (nat2int n)

sanitizeForLatex :: Prelude.String -> Prelude.String
sanitizeForLatex []      = []
sanitizeForLatex ('_':x) = "\\_"++(sanitizeForLatex x)
sanitizeForLatex ('$':x) = "\\$"++(sanitizeForLatex x)
sanitizeForLatex ('#':x) = "\\#"++(sanitizeForLatex x)
sanitizeForLatex (c:x)   = c:(sanitizeForLatex x)

kindToCoreKind :: Kind -> TypeRep.Kind
kindToCoreKind KindStar          = Kind.liftedTypeKind
kindToCoreKind (KindArrow k1 k2) = Kind.mkArrowKind (kindToCoreKind k1) (kindToCoreKind k2)
kindToCoreKind k                 = Prelude.error ((Prelude.++)
                                                    "kindToCoreKind does not know how to handle kind "
                                                                               (kindToString k))
coreKindToKind :: TypeRep.Kind -> Kind
coreKindToKind k =
  case Kind.splitKindFunTy_maybe k of
      Prelude.Just (k1,k2) -> KindArrow (coreKindToKind k1) (coreKindToKind k2)
      Prelude.Nothing -> 
                      if (Kind.isLiftedTypeKind k)   then KindStar
                 else if (Kind.isUnliftedTypeKind k) then KindStar
                 else if (Kind.isArgTypeKind k)      then KindStar
                 else if (Kind.isUbxTupleKind k)     then KindStar
                 else if (Kind.isOpenTypeKind k)     then KindStar
--
-- The "subkinding" in GHC is not dealt with in System FC, and dealing
-- with it is not actually as simple as you'd think.
--
--                 else if (Coercion.isUnliftedTypeKind k) then KindUnliftedType
--                 else if (Coercion.isOpenTypeKind k)     then KindOpenType
--                 else if (Coercion.isArgTypeKind k)      then KindArgType
--                 else if (Coercion.isUbxTupleKind k)     then KindUnboxedTuple
--
                 else if (Kind.isTySuperKind k)      then Prelude.error "coreKindToKind got the kind-of-the-kind-of-types"
                 else                                         Prelude.error ((Prelude.++) "coreKindToKind got an unknown kind: "
                                                                               (Outputable.showSDoc (Outputable.ppr k)))
outputableToString :: Outputable.Outputable a => a -> Prelude.String
outputableToString = (\x -> Outputable.showSDocDebug (Outputable.ppr x))

coreViewDeep :: Type.Type -> Type.Type
coreViewDeep t =
    case t of
      TypeRep.TyVarTy tv       -> TypeRep.TyVarTy tv
      TypeRep.FunTy arg res    -> TypeRep.FunTy (coreViewDeep arg) (coreViewDeep res)
      TypeRep.AppTy fun arg    -> TypeRep.AppTy (coreViewDeep fun) (coreViewDeep arg)
      TypeRep.ForAllTy fun arg -> TypeRep.ForAllTy fun (coreViewDeep arg)
      TypeRep.TyConApp tc tys  -> let t' = TypeRep.TyConApp tc (Prelude.map coreViewDeep tys)
                        in case Type.coreView t' of
                               Prelude.Nothing     -> t'
                               Prelude.Just    t'' -> t''
      TypeRep.PredTy p         -> case Type.coreView t of
                               Prelude.Nothing     -> TypeRep.PredTy p
                               Prelude.Just    t'  -> t'

{-# NOINLINE trace #-}
trace :: Prelude.String -> a -> a
trace msg x = x

--trace = Debug.Trace.trace
--trace msg x = x
--trace msg x = System.IO.Unsafe.unsafePerformIO $ Prelude.return x
--trace s x = x
--trace msg x = System.IO.Unsafe.unsafePerformIO $
--                (Prelude.>>=) (System.IO.hPutStrLn System.IO.stdout msg) (\_ -> Prelude.return x)
--trace msg x = System.IO.Unsafe.unsafePerformIO $
--                (Prelude.>>=) (System.IO.hPutStr System.IO.stdout " ") (\_ -> Prelude.return x)

-- I'm leaving this here (commented out) in case I ever need it again)
--checkTypeEquality :: Type.Type -> Type.Type -> Prelude.Bool
--checkTypeEquality t1 t2 = Type.tcEqType (Type.expandTypeSynonyms t1) (Type.expandTypeSynonyms t2)
