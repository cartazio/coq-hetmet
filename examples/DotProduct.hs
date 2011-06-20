{-# OPTIONS_GHC -XModalTypes -ddump-types -XNoMonoPatBinds -XFlexibleContexts #-}
module DotProduct
where
import GHC.HetMet.GuestLanguage hiding ((-))
import Prelude hiding ( id, (.) )

--------------------------------------------------------------------------------
-- Dot Product
--
--  This shows how to build a two-level program one step at a time by
--  slowly rearranging it until the brackets can be inserted.
--

-- a one-level function to compute the dot product of two vectors
dotproduct :: [Int] -> [Int] -> Int
dotproduct v1 v2 =
  case v1 of
    []     -> 0
    (a:ax) -> case v2 of
                   []     -> 0
                   (b:bx) ->
                       (a*b)+(dotproduct ax bx)

-- A slightly modified version of the dot product: note that we
-- check for zeroes and ones to avoid multiplying.  In a one-level
-- program this yields no advantage, however!
dotproduct' :: [Int] -> [Int] -> Int
dotproduct' v1 v2 =
  case v1 of
    []     -> 0
    (0:ax) -> case v2 of
                   []     -> 0
                   (b:bx) -> (dotproduct' ax bx)
    (1:ax) -> case v2 of
                   []     -> 0
                   (b:bx) -> b+(dotproduct' ax bx)
    (a:ax) -> case v2 of
                   []     -> 0
                   (b:bx) ->
                       (a*b)+(dotproduct' ax bx)

-- A two-level version of the dot product.  Note how we ask for the first
-- vector, then produce a program which is optimized for multiplying
-- by that particular vector.  If there are zeroes or ones in the
-- original vector, we will emit code which is faster than a one-level
-- dot product.

dotproduct'' :: forall g.
                GuestLanguageAdd         g Integer =>
                GuestLanguageMult        g Integer =>
                GuestIntegerLiteral      g         =>
                [Integer] -> <[ [Integer] -> Integer ]>@g
dotproduct'' v1 =
  case v1 of
    []     -> <[ \v2 -> 0 ]>
    (0:ax) -> <[ \v2 -> case v2 of
                          []     -> 0
                          (b:bx) -> ~~(dotproduct'' ax) bx ]>
    (1:ax) -> <[ \v2 -> case v2 of
                          []     -> 0
                          (b:bx) -> b + ~~(dotproduct'' ax) bx ]>

    (a:ax) -> <[ \v2 -> case v2 of
                          []     -> 0
                          (b:bx) -> ~~(guestIntegerLiteral a) * b + ~~(dotproduct'' ax) bx ]>
