{-# OPTIONS_GHC -XModalTypes -XMultiParamTypeClasses -ddump-types -XNoMonoPatBinds  #-}
module GArrowTikZ
where
import Prelude hiding ( id, (.) )

--
-- Render a fully-polymorphic GArrow term as a boxes-and-wires diagram using TikZ
--

{-
instance GArrow GArrowTikZ (,) where
  ga_id            =
  ga_comp      f g =
  ga_second    f   =
  ga_cancell   f   =
  ga_cancelr   f   =
  ga_uncancell f   =
  ga_uncancelr f   =
  ga_assoc     f   =  
  ga_unassoc   f   =  

instance GArrowDrop GArrowTikZ (,) where
  ga_drop      =

instance GArrowCopy GArrowTikZ (,) where
  ga_copy      =

instance GArrowSwap GArrowTikZ (,) where
  ga_swap      =

instance GArrowLoop GArrowTikZ (,) where
  ga_loop      =

instance GArrowLiteral GArrowTikZ (,) where
  ga_literal   =
-}
