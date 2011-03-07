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
import qualified Class
import qualified Data.Char 
import Data.Bits ((.&.), shiftL, (.|.))
import Prelude ( (++), (+), (==), Show, show, Char )
import qualified Prelude
import qualified GHC.Base

-- crude way of casting Coq "error monad" into Haskell exceptions
errOrFail :: OrError a -> a
errOrFail (OK x)    = x
errOrFail (Error s) = Prelude.error s

-- to do: this could be moved into Coq
coreVarToWeakVar :: Var.Var -> WeakVar
coreVarToWeakVar v | Id.isId     v = WExprVar (WeakExprVar v (errOrFail (coreTypeToWeakType (Var.varType v))))
coreVarToWeakVar v | Var.isTyVar v = WTypeVar (WeakTypeVar v (coreKindToKind (Var.varType v)))
coreVarToWeakVar v | Var.isCoVar v = Prelude.error "FIXME coerVarSort not fully implemented"
coreVarToWeakVar _                 =
   Prelude.error "Var.Var that is neither an expression variable, type variable, nor coercion variable!"

nat2int :: Nat -> Prelude.Int
nat2int O     = 0
nat2int (S x) = 1 + (nat2int x)

nat2string :: Nat -> Prelude.String
nat2string n = show (nat2int n)

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
                      if      (Coercion.isLiftedTypeKind k)   then KindType
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

checkTypeEquality :: Type.Type -> Type.Type -> Prelude.Bool
-- checkTypeEquality t1 t2 = Type.coreEqType (coreViewDeep t1) (coreViewDeep t2)
-- checkTypeEquality t1 t2 = Type.tcEqType (coreViewDeep t1) (coreViewDeep t2)
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
