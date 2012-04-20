{-# LANGUAGE FunctionalDependencies, NoMonomorphismRestriction, MultiParamTypeClasses #-}
module GArrowPretty(SourceCode(..),pprGArrow) where
import Prelude hiding (id,(.))
import Control.GArrow
import Control.Category
import Text.PrettyPrint.HughesPJ

-- The Bool flag is to minimize the number of parentheses generated:
-- it is true iff the principal connective is of lower precedence than
-- juxtaposition
data SourceCode a b = SC Bool Doc

instance Category SourceCode where
  id                  = SC False $ text "id"
  (SC _ g) . (SC _ f) = SC True  $ f <+> (text ">>>") $$ g

instance GArrow SourceCode (,) () where
  ga_first     (SC x f) = SC True  $ text "ga_first"
                                     <+> if x then parens f else f
  ga_second    (SC x f) = SC True  $ text "ga_second"
                                     <+> if x then parens f else f
  ga_cancell            = SC False $ text "ga_cancell"
  ga_cancelr            = SC False $ text "ga_cancelr"
  ga_uncancell          = SC False $ text "ga_uncancell"
  ga_uncancelr          = SC False $ text "ga_uncancelr"
  ga_assoc              = SC False $ text "ga_assoc"
  ga_unassoc            = SC False $ text "ga_unassoc"

instance GArrowSwap SourceCode (,) () where
  ga_swap             = SC False $ text "ga_swap"
instance GArrowDrop SourceCode (,) () where
  ga_drop             = SC False $ text "ga_drop"
instance GArrowCopy SourceCode (,) () where
  ga_copy             = SC False $ text "ga_copy"
instance GArrowLoop SourceCode (,) () where
  ga_loopl   (SC x f) = SC True  $ text "ga_loopl" <+> if x then parens f else f
  ga_loopr   (SC x f) = SC True  $ text "ga_loopr" <+> if x then parens f else f

pprGArrow :: SourceCode x y -> Doc
pprGArrow (SC _ doc) = doc

