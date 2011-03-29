{-# OPTIONS_GHC -XModalTypes -ddump-types -XNoMonoPatBinds #-}
module TypeSafeRun
where
import Prelude hiding ( id, (.) )

--------------------------------------------------------------------------------
-- Examples of "running" code; these examples illustrate the sorts of
-- scoping problems that the Taha-Nielsen environment classifiers look
-- for in the context of HOMOGENEOUS metaprogramming.  You can't
-- actually define these functions for ALL generalized arrows -- only
-- those for which you've defined some sort of interpretation in Haskell.

run :: forall a. (forall b. <[a]>@b) -> a
run = undefined

-- the typchecker correctly rejects this bogosity if you uncomment it:
-- bogus = <[ \x -> ~~( run <[ x ]> ) ]>

-- The Calcano-Moggi-Taha paper on environment classifier inference
-- had a special type for closed code and two special expressions
-- "close" and "open".  These are unnecessary in SystemFC1 where we
-- can use higher-rank polymorphism to get the same result (although
-- in truth it's cheating a bit since their type inference is
-- decidable with no annotations, whereas Rank-N inference is not):

data ClosedCode a = ClosedCode (forall b. <[a]>@b)

open :: forall a b. ClosedCode a -> <[a]>@b
open (ClosedCode x) = x

close :: (forall b. <[a]>@b) -> ClosedCode a
close x = ClosedCode x

run_closed :: ClosedCode a -> a
run_closed = undefined
