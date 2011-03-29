{-# OPTIONS_GHC -XModalTypes -XMultiParamTypeClasses -ddump-types -XNoMonoPatBinds  #-}
module GArrowVerilog
where
import Prelude hiding ( id, (.) )

--  
--  Please ignore this; I didn't manage to finish it
--  


{-
-- A verilog module is an SDoc (chunk of text) giving the module's
-- definition.  The UniqueSupply avoids name clashes.
data VerilogModule =
  VerilogModule
    [VerilogModule]     -- dependencies
    String ->           -- module name
    (Tree String ->        -- input port names
     Tree String ->        -- output port names
     SDoc)              -- raw verilog code for the body
    

instance Show VerilogModule where
  show VerilogModule dep name body =
    "module "++name++"(FIXME)"++(body FIXME FIXME)

data VerilogWrappedType a =
  { vwt_rep :: String }

-- A "verilog garrow" from A to B is, concretely, the source code for a
-- verilog module having input ports of type A and output ports of type B;
-- the UniqueSupply lets us generate names.
data GArrowVerilog a b = 
  UniqueSupply ->
  VerilogWrappedType a ->
  VerilogWrappedType b ->
  GArrowVerilog SDoc

instance GArrow GArrowVerilog (,) where
  ga_id            =  VerilogModule [] "ga_id"   (\ inp outp -> zipTree ... "assign "++outp++" = "++inp)
  ga_comp      f g =  VerilogModule [] "ga_comp" 
  ga_first     :: g x y -> g (x ** z) (y ** z)
  ga_second    f   =  ga_comp (ga_comp ga_swap (ga_first f)) ga_swap
  ga_cancell   f   =  VerilogModule [] "ga_cancell" (\ [in1,in2] [outp]      -> "assign "++outp++" = "++in2)
  ga_cancelr   f   =  VerilogModule [] "ga_cancelr" (\ [in1,in2] [outp]      -> "assign "++outp++" = "++in1)
  ga_uncancell f   =  VerilogModule [] "ga_cancelr" (\ [in1]     [out1,out2] -> "assign "++out1++"=1'b0;\n assign"++out2++"="++in1)
  ga_uncancelr f   =  VerilogModule [] "ga_cancelr" (\ [in1]     [out1,out2] -> "assign "++out2++"=1'b0;\n assign"++out1++"="++in1)
  ga_assoc     f   =  
  ga_unassoc   :: g (x**(y**z)) ((x**y)**z)

instance GArrowDrop GArrowVerilog (,) where
  ga_drop      =

instance GArrowCopy GArrowVerilog (,) where
  ga_copy      =

instance GArrowSwap GArrowVerilog (,) where
  ga_swap      =

instance GArrowLoop GArrowVerilog (,) where
  ga_loop      =

instance GArrowLiteral GArrowVerilog (,) where
  ga_literal   =
-}
