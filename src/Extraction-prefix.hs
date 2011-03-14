{-# OPTIONS_GHC -fno-warn-unused-binds  #-}
module CoqPass ( coqPassCoreToString, coqPassCoreToCore )
where
import qualified MkCore
import qualified TysWiredIn
import qualified TysPrim
import qualified Outputable
import qualified PrelNames
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
import qualified Data.Typeable
import Data.Bits ((.&.), shiftL, (.|.))
import Prelude ( (++), (+), (==), Show, show, Char, (.) )
import qualified Prelude
import qualified GHC.Base

-- used for extracting strings
bin2ascii =
  (\ b0 b1 b2 b3 b4 b5 b6 b7 ->
     let f b i = if b then 1 `shiftL` i else 0
     in Data.Char.chr (f b0 0 .|. f b1 1 .|. f b2 2 .|. f b3 3 .|. f b4 4 .|. f b5 5 .|. f b6 6 .|. f b7 7))
--bin2ascii' =
--  (\ f c -> let n = Char.code c in let h i = (n .&. (1 `shiftL` i)) /= 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
--shiftAscii =
--  \ b c -> Data.Char.chr (((Char.code c) `shiftL` 1) .&. 255 .|. if b then 1 else 0)

-- crude way of casting Coq "error monad" into Haskell exceptions
errOrFail :: OrError a -> a
errOrFail (OK x)    = x
errOrFail (Error s) = Prelude.error s

getTyConTyVars :: TyCon.TyCon -> [Var.TyVar]
getTyConTyVars tc = if TyCon.isFunTyCon tc then [] else if TyCon.isPrimTyCon tc then [] else TyCon.tyConTyVars tc

sortAlts :: [(CoreSyn.AltCon,a,b)] -> [(CoreSyn.AltCon,a,b)]
sortAlts x = x -- FIXME

-- to do: this could be moved into Coq
coreVarToWeakVar :: Var.Var -> WeakVar
coreVarToWeakVar v | Id.isId     v = WExprVar (WeakExprVar v (errOrFail (coreTypeToWeakType (Var.varType v))))
coreVarToWeakVar v | Var.isTyVar v = WTypeVar (WeakTypeVar v (coreKindToKind (Var.varType v)))
coreVarToWeakVar v | Var.isCoVar v = WCoerVar (WeakCoerVar v (Prelude.error "FIXME") 
                                                             (Prelude.error "FIXME") (Prelude.error "FIXME"))
coreVarToWeakVar _                 =
   Prelude.error "Var.Var that is neither an expression variable, type variable, nor coercion variable!"

tyConOrTyFun :: TyCon.TyCon -> Prelude.Either TyCon.TyCon TyCon.TyCon
--FIXME: go back to this
--tyConOrTyFun n = if TyCon.isFamInstTyCon n then Prelude.Left n else Prelude.Right n
tyConOrTyFun n = if TyCon.isFamInstTyCon n then Prelude.Left n else Prelude.Left n

tyFunResultKind :: TyCon.TyCon -> Kind
tyFunResultKind tc = coreKindToKind (TyCon.tyConKind tc)

nat2int :: Nat -> Prelude.Int
nat2int O     = 0
nat2int (S x) = 1 + (nat2int x)

natToString :: Nat -> Prelude.String
natToString n = show (nat2int n)

-- only needs to sanitize characters which might appear in Haskell identifiers
sanitizeForLatex :: Prelude.String -> Prelude.String
sanitizeForLatex []    = []
sanitizeForLatex ('_':x) = "\\_"++(sanitizeForLatex x)
sanitizeForLatex ('$':x) = "\\$"++(sanitizeForLatex x)
sanitizeForLatex ('#':x) = "\\#"++(sanitizeForLatex x)
sanitizeForLatex (c:x) = c:(sanitizeForLatex x)

coreKindToKind :: TypeRep.Kind -> Kind
coreKindToKind k =
  case Coercion.splitKindFunTy_maybe k of
      Prelude.Just (k1,k2) -> KindTypeFunction (coreKindToKind k1) (coreKindToKind k2)
      Prelude.Nothing -> 
                      if (Coercion.isLiftedTypeKind k)   then KindType
                 else if (Coercion.isUnliftedTypeKind k) then KindUnliftedType
                 else if (Coercion.isOpenTypeKind k)     then KindOpenType
                 else if (Coercion.isArgTypeKind k)      then KindArgType
                 else if (Coercion.isUbxTupleKind k)     then KindUnboxedTuple
                 else if (Coercion.isTySuperKind k)      then Prelude.error "coreKindToKind got the kind-of-the-kind-of-types"
                 else if (Coercion.isCoSuperKind k)      then Prelude.error "coreKindToKind got the kind-of-the-kind-of-coercions"
                 else                                         Prelude.error ((Prelude.++) "coreKindToKind got an unknown kind: "
                                                                               (Outputable.showSDoc (Outputable.ppr k)))
outputableToString :: Outputable.Outputable a => a -> Prelude.String
outputableToString = (\x -> Outputable.showSDoc (Outputable.ppr x))

-- TO DO: I think we can remove this now
checkTypeEquality :: Type.Type -> Type.Type -> Prelude.Bool
checkTypeEquality t1 t2 = Type.tcEqType (Type.expandTypeSynonyms t1) (Type.expandTypeSynonyms t2)

--showType t = outputableToString (Type.expandTypeSynonyms t)
showType t = outputableToString (coreViewDeep t)

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

-- FIXME: cotycon applications may be oversaturated
coreCoercionToWeakCoercion :: Type.Type -> WeakCoercion
coreCoercionToWeakCoercion c =
 case c of
  TypeRep.TyVarTy  v     -> WCoVar (WeakCoerVar v (Prelude.error "FIXME") (Prelude.error "FIXME") (Prelude.error "FIXME"))
  TypeRep.AppTy    t1 t2 -> WCoApp   (coreCoercionToWeakCoercion t1) (coreCoercionToWeakCoercion t2)
  TypeRep.TyConApp tc t  ->
      case TyCon.isCoercionTyCon_maybe tc of
        Prelude.Nothing -> Prelude.error ((Prelude.++) "coreCoercionToWeakCoercion got " (outputableToString c))
        Prelude.Just (_, ctcd) ->
            case (ctcd,t) of
              (TyCon.CoTrans , [x,y]     ) -> WCoComp   (coreCoercionToWeakCoercion x) (coreCoercionToWeakCoercion y)
              (TyCon.CoSym   , [x]       ) -> WCoSym    (coreCoercionToWeakCoercion x)
              (TyCon.CoLeft  , [x]       ) -> WCoLeft   (coreCoercionToWeakCoercion x)
              (TyCon.CoRight , [x]       ) -> WCoLeft   (coreCoercionToWeakCoercion x)
-- FIXME      (TyCon.CoUnsafe, [t1, t2 ] ) -> WCoUnsafe (coreTypeToWeakType t1) (coreTypeToWeakType t2)
              (TyCon.CoTrans , []        ) -> Prelude.error "CoTrans is not in post-publication-appendix SystemFC1"
              (TyCon.CoCsel1 , []        ) -> Prelude.error "CoCsel1 is not in post-publication-appendix SystemFC1"
              (TyCon.CoCsel2 , []        ) -> Prelude.error "CoCsel2 is not in post-publication-appendix SystemFC1"
              (TyCon.CoCselR , []        ) -> Prelude.error "CoCselR is not in post-publication-appendix SystemFC1"
              (TyCon.CoInst  , []        ) -> Prelude.error "CoInst  is not in post-publication-appendix SystemFC1"
--              (TyCon.CoAxiom , []        ) -> Prelude.error "CoAxiom is not yet implemented (FIXME)"
              _ -> Prelude.error ((Prelude.++) "coreCoercionToWeakCoercion got " (outputableToString c))
  _ -> Prelude.error ((Prelude.++) "coreCoercionToWeakCoercion got " (outputableToString c))
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