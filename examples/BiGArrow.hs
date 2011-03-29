{-# OPTIONS_GHC -XModalTypes -XMultiParamTypeClasses -ddump-types -XNoMonoPatBinds -XFlexibleInstances -XGADTs -XUndecidableInstances #-}
module BiGArrow
where
import GHC.HetMet.GArrow
import Control.Category
import Control.Arrow
import Prelude hiding ( id, (.) )



--------------------------------------------------------------------------------
-- BiGArrows

class GArrow g (**) u => BiGArrow g (**) u where
  -- Note that we trust the user's pair of functions actually are
  -- mutually inverse; confirming this in the type system would
  -- require very powerful dependent types (such as Coq's).  However,
  -- the consequences of failure here are much more mild than failures
  -- in BiArrow.inv: if the functions below are not mutually inverse,
  -- the LoggingBiGArrow will simply compute the wrong result rather
  -- than fail in some manner outside the language's semantics.
  biga_arr :: (x -> y) -> (y -> x) -> g x y
  biga_inv :: g x y -> g y x




--------------------------------------------------------------------------------
-- GArrow-pairs are BiGArrows (but not a GArrowDrop!)

-- For any GArrow instance, its mutually inverse pairs form a BiGArrow
data GArrow g (**) u => GArrowInversePair g (**) u x y =
    GArrowInversePair { forward :: g x y , backward :: g y x }
instance GArrow g (**) u => Category (GArrowInversePair g (**) u) where
  id    = GArrowInversePair { forward = id , backward = id }
  f . g = GArrowInversePair { forward = (forward f) . (forward g) , backward = (backward g) . (backward f) }
instance GArrow g (**) u => GArrow (GArrowInversePair g (**) u) (**) u where
  ga_first     f = GArrowInversePair { forward = ga_first  (forward f), backward = ga_first  (backward f) }
  ga_second    f = GArrowInversePair { forward = ga_second (forward f), backward = ga_second (backward f) }
  ga_cancell     = GArrowInversePair { forward = ga_cancell           , backward = ga_uncancell }
  ga_cancelr     = GArrowInversePair { forward = ga_cancelr           , backward = ga_uncancelr }
  ga_uncancell   = GArrowInversePair { forward = ga_uncancell         , backward = ga_cancell   }
  ga_uncancelr   = GArrowInversePair { forward = ga_uncancelr         , backward = ga_cancelr   }
  ga_assoc       = GArrowInversePair { forward = ga_assoc             , backward = ga_unassoc   }
  ga_unassoc     = GArrowInversePair { forward = ga_unassoc           , backward = ga_assoc     }
instance GArrowSwap g (**) u => GArrowSwap (GArrowInversePair g (**) u) (**) u where
  ga_swap = GArrowInversePair { forward = ga_swap , backward = ga_swap }
-- but notice that we can't (in general) get
-- instance GArrowDrop g => GArrowDrop (GArrowInversePair g) where ...




--------------------------------------------------------------------------------
-- BCPierce's symmetric lenses form a BiGArrow *with* GArrowSwap


-- NOTE: if you uncomment, this BE SURE YOU ARE NOT USING -fcoqpass --
-- the code below will trigger one of the not-yet-fixed bugs in the
-- code that turns GHC CoreSyn into strongly-typed Coq expressions.

{-
data Lens x y where
  Lens :: forall x y c1 c2 . ((x,c1)->(y,c2)) -> ((y,c2)->(x,c1)) -> Lens x y

-- can we make lenses out of GArrows other than (->)?
instance Category Lens where
  id                          = Lens (\x -> x) (\x -> x)
  (Lens g1 g2) . (Lens f1 f2) = Lens (\(x,(c1,c2)) -> let (y,fc) = f1 (x,c1) in  let (z,gc) = g1 (y,c2) in  (z,(fc,gc)))
                                     (\(z,(c1,c2)) -> let (y,gc) = g2 (z,c2) in  let (x,fc) = f2 (y,c1) in  (x,(fc,gc)))

instance GArrow Lens (,) () where
  ga_first     (Lens f1 f2) = Lens (\((x1,x2),c) -> let (y,c') = f1 (x1,c) in ((y,x2),c'))
                                   (\((x1,x2),c) -> let (y,c') = f2 (x1,c) in ((y,x2),c'))
  ga_second    (Lens f1 f2) = Lens (\((x1,x2),c) -> let (y,c') = f1 (x2,c) in ((x1,y),c'))
                                   (\((x1,x2),c) -> let (y,c') = f2 (x2,c) in ((x1,y),c'))
  ga_cancell                = Lens (\(((),x),()) -> (    x ,())) 
                                   (\(    x ,()) -> (((),x),()))
  ga_uncancell              = Lens (\(    x ,()) -> (((),x),()))
                                   (\(((),x),()) -> (    x ,())) 
  ga_cancelr                = Lens (\((x,()),()) -> (    x ,())) 
                                   (\( x    ,()) -> ((x,()),()))
  ga_uncancelr              = Lens (\( x    ,()) -> ((x,()),()))
                                   (\((x,()),()) -> (    x ,())) 
  ga_assoc                  = Lens (\(((x,y),z),()) -> ((x,(y,z)),()))
                                   (\((x,(y,z)),()) -> (((x,y),z),()))
  ga_unassoc                = Lens (\((x,(y,z)),()) -> (((x,y),z),()))
                                   (\(((x,y),z),()) -> ((x,(y,z)),()))

instance GArrowDrop Lens (,) () where
  ga_drop        = Lens (\(x,()) -> ((),x)) (\((),x) -> (x,()))
instance GArrowCopy Lens (,) () where
  ga_copy        = Lens (\(x,()) -> ((x,x),())) (\((x,_),()) -> (x,()))
instance GArrowSwap Lens (,) () where
  ga_swap        = Lens (\((x,y),()) -> ((y,x),())) (\((x,y),()) -> ((y,x),()))

instance BiGArrow Lens (,) () where
  biga_arr f f'  = Lens (\(x,()) -> ((f x),())) (\(x,()) -> ((f' x),()))
  biga_inv (Lens f1 f2) = Lens f2 f1
-}
