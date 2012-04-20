{-# OPTIONS_GHC -XModalTypes -XScopedTypeVariables -XFlexibleContexts -XMultiParamTypeClasses -ddump-types -XNoMonoPatBinds #-}
module GArrowTutorial
where
import Data.Bits
import Data.Bool (not)
import Control.GArrow
import GHC.HetMet.GuestLanguage hiding ( (-) )
import Control.Category
import Control.Arrow
import Prelude hiding ( id, (.) )

-- The best way to understand heterogeneous metaprogramming and
-- generalized arrows is to play around with this file, poking at the
-- examples until they fail to typecheck -- you'll learn a lot that
-- way!

-- Once you've built the modified compiler, you can compile this file
-- with:
--
--    $ inplace/bin/ghc-stage2 tutorial.hs
--

-- -XModalTypes adds a new syntactical expression, "code brackets":
code_fst = <[ \(x,y) -> x ]>

-- This new expression is the introduction form for modal types:
code_fst :: forall a b g. <[ (a,b) -> a ]>@g

-- Think of <[T]>@g as being the type of programs written in language
-- "g" which, when "executed", return a value of type "T".  I mention
-- "language g" because the *heterogeneous* aspect of HetMet means
-- that we can limit the sorts of constructs allowed inside the code
-- brackets, permitting only a subset of Haskell (you have to use
-- Haskell syntax, though).

-- There is a second new expression form, "~~", called "escape":

code_fst_fst = <[ \z -> ~~code_fst (~~code_fst z) ]>

-- Note that ~~ binds more tightly than any other operator.  There is
-- an alternate version, "~~$", which binds more weakly than any other
-- operator (this is really handy sometimes!).  To demonstrate this,
-- the next two expressions differ only in superficial syntax:

example1    foo bar = <[ ~~$ foo bar  ]>
example2    foo bar = <[ ~~( foo bar) ]>
-- example3 foo bar = <[ ~~  foo bar  ]>

-- ... but the third one is completely different (and in fact, doesn't
-- even parse, but we'll get to that in a moment)

-- The escape operation must appear within code brackets.  In truth,
-- it is really a "hole" punched in the code brackets -- the thing to
-- which the escape operator gets applied is typed as if it were
-- *outside* the code brackets.  It must have type <[T]>, and the
-- escape operator allows it to be used *inside* code brackets as if
-- it had type "T".

-- So, the escape operator is basically a way of pasting code
-- fragments into each other.

-- This is where those type variables after the "@" sign come in: if
-- you paste two pieces of code into a third, all three must be
-- written in the same language.  We express this by unifying their
-- tyvars:

compose_code :: forall g a b c. <[a->b]>@g -> <[b->c]>@g -> <[a->c]>@g
compose_code x y = <[ \z -> ~~y (~~x z) ]>

-- Now, try commenting out the type ascription above and uncommenting
-- any of these three:
--
-- compose_code :: forall g h a b c. <[a->b]>@h -> <[b->c]>@g -> <[a->c]>@g
-- compose_code :: forall g h a b c. <[a->b]>@g -> <[b->c]>@h -> <[a->c]>@g
-- compose_code :: forall g h a b c. <[a->b]>@g -> <[b->c]>@g -> <[a->c]>@h
--

-- The typechecker won't let you get away with that -- you're trying
-- to force a type which is "too polymorphic" onto paste2.  If the
-- compiler allowed that, the resulting metaprogram might try to
-- splice together programs written in different languages, resulting
-- in mayhem.

-- NEW SCOPING RULES: The syntactical depth (or just "depth") of an
-- expression is the number of surrounding code-brackets minus the
-- number of surrounding escapes (this is strictly a syntax concept
-- and has NOTHING to do with the type system!).  It is very important
-- to keep in mind that the scope of a bound variable extends only to
-- expressions at the same depth!  To demonstrate, the following
-- expression will fail to parse:

-- badness = \x -> <[ x ]>

-- ...and in the following expression, the occurrence of "x" is bound
-- by the first (outer) lambda, not the second one:

no_shadowing_here = \x -> <[ \x -> ~~x ]>

-- Lastly, you can wrap code-brackets around an identifier in a
-- top-level, let, or where binding.  Notice how GHC doesn't complain
-- here about defining an identifier twice!

foo       =    \x         -> x+1
<[ foo ]> = <[ \(x::Bool) -> x   ]>

-- Now you can use foo (the second one!) inside code-brackets:

bar x = <[ foo ~~x ]>

bar :: forall g. <[Bool]>@g -> <[Bool]>@g

-- In fact, the identifiers have completely unrelated types.  Which
-- brings up another important point: types are ALWAYS assigned
-- "relative to" depth zero.  So although we imagine "foo" existing at
-- depth-one, its type is quite firmly established as <[ Bool -> Bool ]>

-- It has to be this way -- to see why, consider a term which is more
-- polymorphic than "foo":

<[ foo' ]> = <[ \x -> x ]>

-- Its type is:

<[ foo' ]> :: forall a g . <[ a -> a ]>@g

-- ...and there's no way to express the g-polymorphism entirely from
-- within the brackets.

-- So why does all of this matter?  Mainly so that we can continue to use .  We'd like
-- the "+" operator to work "as expected" -- in other words, we'd like
-- people to be able to write things like

increment_at_level1 = <[ \x -> x + 1 ]>

-- However, in unmodified haskell an identifier like (+) may have only
-- one type.  In this case that type is:
--
--     (+) :: Num a => a -> a -> a
--
-- Now, we could simply decree that when (+) appears inside code
-- brackets, an "implicit ~~" is inserted, so the desugared expression
-- is:
--
--    increment_at_level1 = <[ \x -> ~~(+) x 1 ]> 
--
-- unfortunately this isn't going to work for guest languages that
-- don't have higher-order functions.  Haskell uses curried arguments
-- because it has higher-order functions, but in a first-order guest
-- language a more sensible type for (+) would be:
--
--    (+) :: Num a => (a,a) -> a
-- 
-- ... or even something less polymorphic, like
--
--    (+) :: (Int,Int) -> Int
--
-- so to maintain flexibility, we allow an identifier to have
-- different types at different syntactic depths; this way type
-- choices made for Haskell don't get imposed on guest languages that
-- are missing some of its features.
-- 
-- In hindsight, what we REALLY want is for increment_at_level1 to
-- be desugared like this (much like the Arrow (|...|) syntax):
--
--   increment_at_level1 = <[ \x -> ~~( <[x]> + <[1]> ) ]>
--
-- ... because then we can declare
--
--   instance Num a => Num <[a]> where ...
--
-- or just
--
--   instance Num <[Int]> where ...
--
-- unfortunately there's a major problem: knowing how to do this sort
-- of desugaring requires knowing the *arity* of a function.  For
-- symbols we can kludge it by checking Haskell's parsing rules (there
-- are only a handful of unary symbols; all others are binary), but
-- this is crude and won't work at all for non-symbol identifiers.
-- And we can look at a type like x->y->z and say "oh, that's a
-- two-argument function", but sometimes GHC doesn't know the complete
-- type of an identifier in the midst of unification (i.e. "x has type
-- Int->a for some a, where a could be Int or Int->Int"), so guessing
-- the arity from the type cannot be done during parsing, which is
-- when we need to do this.
--
-- Okay, I think that's more or less a brain dump of why I changed the
-- scoping rules and the problems with the other solutions I tried.
--
-- I am very interested in hearing any suggestions on better ways of
-- dealing with this, so long as you can still use operators like (+)
-- in guest languages without higher-order functions.
--

--------------------------------------------------------------------------------
-- Ye Olde and Most Venerable "pow" Function

pow :: forall c. GuestIntegerLiteral c => GuestLanguageMult c Integer => Integer -> <[ Integer -> Integer ]>@c
pow n =
   if n==0
   then <[ \x -> 1 ]>
   else <[ \x -> x * ~~(pow (n - 1)) x ]>


-- a more efficient two-level pow
pow' :: forall c. GuestIntegerLiteral c => GuestLanguageMult c Integer => Integer -> <[ Integer -> Integer ]>@c
pow' 0  = <[ \x -> 1 ]>
pow' 1  = <[ \x -> x ]>
pow' n  = if   n `mod` 2==0
          then <[ \x -> (\y -> y*y) (~~(pow' $ n `shiftR` 2) x) ]>
          else <[ \x -> x * ~~(pow' $ n-1) x ]>



