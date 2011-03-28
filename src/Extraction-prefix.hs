module CoqPass ( coqPassCoreToString, coqPassCoreToCore )
where
import qualified Unique
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
import qualified TyCon
import qualified Coercion
import qualified Var
import qualified Id
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
import Prelude ( (++), (+), (==), Show, show, Char, (.), ($) )
import qualified Prelude
import qualified Debug.Trace
import qualified GHC.Base
import qualified System.IO
import qualified System.IO.Unsafe

{-  -- used for extracting strings WITHOUT the patch for Coq
bin2ascii =
  (\ b0 b1 b2 b3 b4 b5 b6 b7 ->
     let f b i = if b then 1 `shiftL` i else 0
     in Data.Char.chr (f b0 0 .|. f b1 1 .|. f b2 2 .|. f b3 3 .|. f b4 4 .|. f b5 5 .|. f b6 6 .|. f b7 7))
-}

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

-- to do: this could be moved into Coq
coreVarToWeakVar :: Var.Var -> WeakVar
coreVarToWeakVar v | Id.isId     v = WExprVar (WeakExprVar v (errOrFail (coreTypeToWeakType (Var.varType v))))
coreVarToWeakVar v | Var.isTyVar v = WTypeVar (WeakTypeVar v (coreKindToKind (Var.varType v)))
coreVarToWeakVar v | Var.isCoVar v = WCoerVar (WeakCoerVar v (Prelude.error "FIXME") 
                                                             (Prelude.error "FIXME") (Prelude.error "FIXME"))
coreVarToWeakVar _                 =
   Prelude.error "Var.Var that is neither an expression variable, type variable, nor coercion variable!"

errOrFail (OK x)    = x
errOrFail (Error s) = Prelude.error s

tyConOrTyFun :: TyCon.TyCon -> Prelude.Either TyCon.TyCon TyCon.TyCon
tyConOrTyFun n =
   if n == TysPrim.statePrimTyCon     -- special-purpose hack treat State# as a type family since it has kind *->* but no tyvars
   then Prelude.Right n
   else if TyCon.isFamInstTyCon n
        then Prelude.Right n
        else Prelude.Left n

nat2int :: Nat -> Prelude.Int
nat2int O     = 0
nat2int (S x) = 1 + (nat2int x)

natToString :: Nat -> Prelude.String
natToString n = show (nat2int n)

-- only needs to sanitize characters which might appear in Haskell identifiers
sanitizeForLatex :: Prelude.String -> Prelude.String
sanitizeForLatex []      = []
sanitizeForLatex ('_':x) = "\\_"++(sanitizeForLatex x)
sanitizeForLatex ('$':x) = "\\$"++(sanitizeForLatex x)
sanitizeForLatex ('#':x) = "\\#"++(sanitizeForLatex x)
sanitizeForLatex (c:x)   = c:(sanitizeForLatex x)

kindToCoreKind :: Kind -> TypeRep.Kind
kindToCoreKind KindStar          = TypeRep.liftedTypeKind
kindToCoreKind (KindArrow k1 k2) = Coercion.mkArrowKind (kindToCoreKind k1) (kindToCoreKind k2)
kindToCoreKind _                 = Prelude.error "kindToCoreKind does not know how to handle that"

coreKindToKind :: TypeRep.Kind -> Kind
coreKindToKind k =
  case Coercion.splitKindFunTy_maybe k of
      Prelude.Just (k1,k2) -> KindArrow (coreKindToKind k1) (coreKindToKind k2)
      Prelude.Nothing -> 
                      if (Coercion.isLiftedTypeKind k)   then KindStar
                 else if (Coercion.isUnliftedTypeKind k) then KindStar
                 else if (Coercion.isArgTypeKind k)      then KindStar
                 else if (Coercion.isUbxTupleKind k)     then KindStar
                 else if (Coercion.isOpenTypeKind k)     then KindStar
--                 else if (Coercion.isUnliftedTypeKind k) then KindUnliftedType
--                 else if (Coercion.isOpenTypeKind k)     then KindOpenType
--                 else if (Coercion.isArgTypeKind k)      then KindArgType
--                 else if (Coercion.isUbxTupleKind k)     then KindUnboxedTuple
                 else if (Coercion.isTySuperKind k)      then Prelude.error "coreKindToKind got the kind-of-the-kind-of-types"
                 else if (Coercion.isCoSuperKind k)      then Prelude.error "coreKindToKind got the kind-of-the-kind-of-coercions"
                 else                                         Prelude.error ((Prelude.++) "coreKindToKind got an unknown kind: "
                                                                               (Outputable.showSDoc (Outputable.ppr k)))
outputableToString :: Outputable.Outputable a => a -> Prelude.String
outputableToString = (\x -> Outputable.showSDoc (Outputable.ppr x))

-- I'm leaving this here (commented out) in case I ever need it again)
--checkTypeEquality :: Type.Type -> Type.Type -> Prelude.Bool
--checkTypeEquality t1 t2 = Type.tcEqType (Type.expandTypeSynonyms t1) (Type.expandTypeSynonyms t2)

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

coreCoercionToWeakCoercion :: Type.Type -> WeakCoercion
coreCoercionToWeakCoercion c =
 WCoUnsafe (errOrFail (coreTypeToWeakType t1)) (errOrFail (coreTypeToWeakType t2))
   where
    (t1,t2) = Coercion.coercionKind c
{-
-- REMEMBER: cotycon applications may be oversaturated
 case c of
  TypeRep.TyVarTy  v     -> WCoVar (WeakCoerVar v (Prelude.error "FIXME") (Prelude.error "FIXME") (Prelude.error "FIXME"))
  TypeRep.AppTy    t1 t2 -> WCoApp   (coreCoercionToWeakCoercion t1) (coreCoercionToWeakCoercion t2)
  TypeRep.TyConApp tc t  ->
      case TyCon.isCoercionTyCon_maybe tc of
        Prelude.Nothing -> Prelude.error ((Prelude.++) "coreCoercionToWeakCoercion got isCoercionTyCon_maybe " (outputableToString c))
        Prelude.Just (_, ctcd) ->
            case (ctcd,t) of
              (TyCon.CoTrans , [x,y]     ) -> WCoComp   (coreCoercionToWeakCoercion x) (coreCoercionToWeakCoercion y)
              (TyCon.CoSym   , [x]       ) -> WCoSym    (coreCoercionToWeakCoercion x)
              (TyCon.CoLeft  , [x]       ) -> WCoLeft   (coreCoercionToWeakCoercion x)
              (TyCon.CoRight , [x]       ) -> WCoLeft   (coreCoercionToWeakCoercion x)
--            (TyCon.CoUnsafe, [t1, t2 ] ) -> WCoUnsafe (coreTypeToWeakType t1) (coreTypeToWeakType t2)
              (TyCon.CoTrans , []        ) -> Prelude.error "CoTrans is not in post-publication-appendix SystemFC1"
              (TyCon.CoCsel1 , []        ) -> Prelude.error "CoCsel1 is not in post-publication-appendix SystemFC1"
              (TyCon.CoCsel2 , []        ) -> Prelude.error "CoCsel2 is not in post-publication-appendix SystemFC1"
              (TyCon.CoCselR , []        ) -> Prelude.error "CoCselR is not in post-publication-appendix SystemFC1"
              (TyCon.CoInst  , []        ) -> Prelude.error "CoInst  is not in post-publication-appendix SystemFC1"
              (TyCon.CoAxiom _ _ _ , _   ) -> Prelude.error "CoAxiom is not yet implemented (FIXME)"
              ( _, [ t1 , t2 ]) -> WCoUnsafe (errOrFail (coreTypeToWeakType t1)) (errOrFail (coreTypeToWeakType t2))
              _ -> Prelude.error ((Prelude.++) "coreCoercionToWeakCoercion got " (outputableToString c))
  _ -> Prelude.error ((Prelude.++) "coreCoercionToWeakCoercion got " (outputableToString c))
-}
--  TypeRep.ForAllTy v t   -> WCoAll  (Prelude.error "FIXME") (coreTypeToWeakType t)
-- FIXME   x y                                  -> WCoAppT    (coreCoercionToWeakCoercion x) (coreCoercionToWeakType y)
--  CoreSyn.Type t                            -> WCoType   (coreTypeToWeakType t)

{-
weakCoercionToCoreCoercion :: CoreCoercion -> Type.Type
| WCoVar     (weakCoerVar _ _ t1 t2) => (t1,t2)
| WCoType    t                       => Prelude_error "FIXME WCoType"
| WCoApp     c1 c2                   => Prelude_error "FIXME WCoApp"
| WCoAppT    c t                     => Prelude_error "FIXME WCoAppT"
| WCoAll     k f                     => Prelude_error "FIXME WCoAll"
| WCoSym     c                       => let (t2,t1) := weakCoercionTypes c in (t1,t2)
| WCoComp    c1 c2                   => Prelude_error "FIXME WCoComp"
| WCoLeft    c                       => Prelude_error "FIXME WCoLeft"
| WCoRight   c                       => Prelude_error "FIXME WCoRight"
| WCoUnsafe  t1 t2                   => (t1,t2)
-}


--trace = Debug.Trace.trace
--trace msg x = x
trace msg x = System.IO.Unsafe.unsafePerformIO $ Prelude.return x
{-
trace s x = x
trace msg x = System.IO.Unsafe.unsafePerformIO $
                (Prelude.>>=) (System.IO.hPutStrLn System.IO.stdout msg) (\_ -> Prelude.return x)
trace msg x = System.IO.Unsafe.unsafePerformIO $
                (Prelude.>>=) (System.IO.hPutStr System.IO.stdout " ") (\_ -> Prelude.return x)
-}
