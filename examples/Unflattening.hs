{-# OPTIONS_GHC -XModalTypes -ddump-types -XNoMonoPatBinds -XMultiParamTypeClasses #-}
module Unflattening
where
import GHC.HetMet.CodeTypes hiding ((-))
import Control.GArrow
import Control.Category
import Control.Arrow
import Prelude hiding ( id, (.) )

--------------------------------------------------------------------------------
-- Unflattening

-- The current implementation has problems with literals at level>0;
-- there are special-purpose hacks for Int and Char, but none for
-- unit.  So I use this instead as a placeholder for <[ () ]>

<[ u ]> = Prelude.error "FIXME"

-- This more or less "undoes" the flatten function.  People often ask
-- me how you "translate generalized arrows back into multi-level
-- terms".. I'm not sure why you'd want to do that, but this is how:

newtype Code x y = Code { unCode :: forall a. <[ x -> y ]>@a }

instance Category Code where
  id             = Code <[ \x -> x ]>
  f . g          = Code <[ \x -> ~~(unCode f) (~~(unCode g) x) ]>

instance GArrow Code (,) () where
  ga_first     f = Code <[ \(x,y) -> ((~~(unCode f) x),y) ]>
  ga_second    f = Code <[ \(x,y) -> (x         ,(~~(unCode f) y)) ]>
  ga_cancell     = Code <[ \(_,x) -> x ]>

  ga_cancelr     = Code <[ \(x,_) -> x ]>
  ga_uncancell   = Code <[ \x -> (u,x) ]>
  ga_uncancelr   = Code <[ \x -> (x,u) ]>
  ga_assoc       = Code <[ \((x,y),z) -> (x,(y,z)) ]>
  ga_unassoc     = Code <[ \(x,(y,z)) -> ((x,y),z) ]>

instance GArrowDrop Code (,) () where
  ga_drop        = Code <[ \_ -> u ]>

instance GArrowCopy Code (,) () where
  ga_copy        = Code <[ \x -> (x,x) ]>

instance GArrowSwap Code (,) () where
  ga_swap        = Code <[ \(x,y) -> (y,x) ]>
