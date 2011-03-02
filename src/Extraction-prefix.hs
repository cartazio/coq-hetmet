{-# OPTIONS_GHC -fno-warn-unused-binds  #-}
module Extraction ( coqCoreToStringPass )
where
--import HsSyn
--import TcType
--import CoreFVs
--import CoreUtils
--import MkCore
--import Var
--import BasicTypes
--import Bag
--import VarSet
--import SrcLoc
--import Data.List

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

{-
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
coreVarSort :: Var.Var -> CoreVarSort
coreVarSort v | Id.isId     v = CoreExprVar (Var.varType{-AsType-} v)
coreVarSort v | Var.isTyVar v = CoreTypeVar (coreKindToKind (Var.varType v))
coreVarSort v | Var.isCoVar v = CoreCoerVar (Coercion.coercionKind v)
coreVarSort v | otherwise     = Prelude.error "Var.Var that is neither an expression variable, type variable, nor coercion variable!"

outputableToString :: Outputable -> String
outputableToString = (\x -> Outputable.showSDoc (Outputable.ppr x))
-}
