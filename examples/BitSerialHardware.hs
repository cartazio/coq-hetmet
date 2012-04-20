{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}
module BitSerialHardware(Wire,BitSerialHardwarePrimitives(..)) where
import Control.GArrow
import Control.Category
import GArrowPretty
import Prelude hiding (id, (.))
import Text.PrettyPrint.HughesPJ

------------------------------------------------------------------------------
-- Bit-Serial Hardware Primitives

data Wire = Wire

class (GArrowSwap v (,) (), GArrowDrop v (,) (), GArrowCopy v (,) (), GArrowLoop v (,) ()) =>
      BitSerialHardwarePrimitives v where
  high    :: v () Wire
  low     :: v () Wire

  not     :: v Wire        Wire
  xor     :: v (Wire,Wire) Wire
  or      :: v (Wire,Wire) Wire
  and     :: v (Wire,Wire) Wire
  mux2    :: v (Wire,(Wire,Wire)) Wire
  maj3    :: v (Wire,(Wire,Wire)) Wire
  reg     :: v Wire Wire

  loop    :: [Bool] -> v () Wire
  fifo    ::    Int -> v Wire Wire

  probe   ::    Int -> v Wire Wire
  oracle  ::    Int -> v ()        Wire

instance BitSerialHardwarePrimitives SourceCode where
  high        = SC False $ text "high"
  low         = SC False $ text "low"
  not         = SC False $ text "not"
  xor         = SC False $ text "xor"
  or          = SC False $ text "or"
  and         = SC False $ text "and"
  mux2        = SC False $ text "mux2"
  maj3        = SC False $ text "maj3"
  reg         = SC False $ text "reg"
  loop   vals = SC False $ text "loop"   <+> (brackets $ hcat $ punctuate comma $ map (text . show) vals)
  fifo   len  = SC False $ text "fifo"   <+> (text . show) len
  probe  id   = SC False $ text "probe"  <+> (text . show) id
  oracle id   = SC False $ text "oracle" <+> (text . show) id

