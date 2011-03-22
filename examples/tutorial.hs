{-# OPTIONS_GHC -XModalTypes -XScopedTypeVariables -XFlexibleContexts -XMultiParamTypeClasses -ddump-types -XNoMonoPatBinds -XFlexibleInstances -XGADTs -XUndecidableInstances #-}
module GArrowsTutorial
where
import Data.Bits
import Data.Bool (not)
import GHC.HetMet.CodeTypes hiding ((-))
import GHC.HetMet.GArrow
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






-- The rest of this file contains a bunch of example programs:
-- exponentiation, dot-product, a bunch of classic MetaML idioms, and
-- a translation of Nanevski+Pfenning's two-stage regex matcher.






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




--------------------------------------------------------------------------------
-- Taha-Sheard "isomorphism for code types"

back  :: forall a b c. (<[b]>@a -> <[c]>@a) -> <[ b->c ]>@a
back  = \f -> <[ \x -> ~~(f <[x]>) ]>

forth :: forall a b c. <[b->c]>@a -> (<[b]>@a -> <[c]>@a)
forth = \f -> \x -> <[ ~~f ~~x ]>



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



--------------------------------------------------------------------------------
-- A two-level Regular Expression matcher, adapted from Nanevski+Pfenning, Figure 6
data Regex
 = Empty
 | Plus  Regex Regex 
 | Times Regex Regex
 | Star  Regex
 | Const Char

class Stream a where
  s_empty :: a -> Bool
  s_head  :: a -> Char
  s_tail  :: a -> a

-- a continuation-passing-style matcher

accept :: Stream s => Regex -> (s -> Bool) -> s -> Bool

accept Empty k s          =
  k s

accept (Plus e1 e2) k s   =
 (accept e1 k s) || (accept e2 k s)

accept (Times e1 e2) k s  =
 (accept e1 (accept e2 k)) s

accept (Star e) k s       =
 (k s) || (accept e (\s' -> accept (Star e) k s') s)
 -- FIXME: this will loop forever if you give it (Star x) where x can
 -- match the empty string

accept (Const c) k s      =
 if s_empty s 
 then False
 else (s_head s) == c && k (s_tail s)

class GuestStream g a where
  <[ gs_empty ]> :: <[ a -> Bool ]>@g
  <[ gs_head  ]> :: <[ a -> Char ]>@g
  <[ gs_tail  ]> :: <[ a -> a    ]>@g

class GuestEqChar g where
  <[ (==) ]> :: <[ Char -> Char -> Bool ]>@g
{-
staged_accept ::
    Regex
    -> forall c s.
         GuestStream c s =>
         GuestCharLiteral c =>
         GuestLanguageBool c =>
         GuestEqChar c =>
         <[ s -> Bool ]>@c
      -> <[ s -> Bool ]>@c

staged_accept Empty k            =
   <[ \s -> gs_empty s ]>

-- note that code for "k" gets duplicated here
staged_accept (Plus e1 e2) k     =
   <[ \s -> (~~(staged_accept e1 k) s) || (~~(staged_accept e2 k) s) ]>

staged_accept (Times e1 e2) k    =
   <[ \s -> ~~(staged_accept e1 (staged_accept e2 k)) s ]>

staged_accept (Star e) k         =
   loop
    where
    -- loop :: <[s -> Bool]>@g
     loop =  <[ \s -> ~~k s || ~~(staged_accept e loop) s ]>
    -- note that loop is not (forall c s. <[s -> Bool]>@c)
    -- because "k" is free in loop; it is analogous to the free
    -- environment variable in Nanevski's example


staged_accept (Const c) k        =
    <[ \s -> if gs_empty s 
             then false
             else (gs_head s) == ~~(guestCharLiteral c) && ~~k (gs_tail s) ]>
-}

-- this type won't work unless the case for (Star e) is commented out;
-- see loop above
--      Regex
--      -> (forall c s.
--          GuestStream c s =>
--          GuestLanguageBool c =>
--          GuestEqChar c =>
--          <[s -> Bool]>@c)
--     -> (forall c s.
--          GuestStream c s =>
--          GuestLanguageBool c =>
--          GuestEqChar c =>
--          <[s -> Bool]>@c)




--------------------------------------------------------------------------------
-- Unflattening

{-
-- This more or less "undoes" the flatten function.  People often ask
-- me how you "translate generalized arrows back into multi-level
-- terms".. I'm not sure why you'd want to do that, but this is how:
newtype Code x y = Code { unCode :: forall a. <[ x -> y ]>@a }

instance Category Code where
  id             = Code <[ \x -> x ]>
  f . g          = Code <[ \x -> ~~(unCode f) (~~(unCode g) x) ]>

instance GArrow Code (,) where
  ga_first     f = Code <[ \(x,y) -> ((~~(unCode f) x),y) ]>
  ga_second    f = Code <[ \(x,y) -> (x         ,(~~(unCode f) y)) ]>
  ga_cancell     = Code <[ \(_,x) -> x ]>

  ga_cancelr     = Code <[ \(x,_) -> x ]>
  ga_uncancell   = Code <[ \x -> (%%(),x) ]>
  ga_uncancelr   = Code <[ \x -> (x,%%()) ]>
  ga_assoc       = Code <[ \((x,y),z) -> (x,(y,z)) ]>
  ga_unassoc     = Code <[ \(x,(y,z)) -> ((x,y),z) ]>
-}



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
{-
instance (GArrowDrop g (**) u, GArrowCopy g (**) u) => GArrowCopy (GArrowInversePair g (**) u) (**) u where
  ga_copy = GArrowInversePair { forward = ga_copy , backward = ga_second ga_drop >>> ga_cancelr }
-}
-- but notice that we can't (in general) get
-- instance GArrowDrop g => GArrowDrop (GArrowInversePair g) where ...

{-
-- For that, we need PreLenses, which "log the history" where necessary.
-- I call this a "PreLens" because it consists of the data required
-- for a Lens (as in BCPierce's Lenses) but does not necessarily
-- satisfy the putget/getput laws.  Specifically, the "extra stuff" we
-- store is the inversion function.
newtype PreLens x y = PreLens { preLens :: x -> (y , y->x) }

instance Category PreLens where
  id    = PreLens { preLens = \x -> (x, (\x -> x)) }
  f . g = PreLens { preLens = \x -> let (gx,g') = (preLens g) x in let (fgx,f') = (preLens f) gx in (fgx , \q -> g' (f' q)) }

instance GArrow PreLens (,) where
  ga_first     f = PreLens { preLens = \(x,z) -> let (y,f') = (preLens f) x in ((y,z),(\(q1,q2) -> (f' q1,q2))) }
  ga_second    f = PreLens { preLens = \(z,x) -> let (y,f') = (preLens f) x in ((z,y),(\(q1,q2) -> (q1,f' q2))) }
  ga_cancell     = PreLens { preLens = \(_,x) -> (x,            (\x -> ((),x))) }
  ga_cancelr     = PreLens { preLens = \(x,_) -> (x,            (\x -> (x,()))) }
  ga_uncancell   = PreLens { preLens = \x     -> (((),x),       (\(_,x) -> x)) }
  ga_uncancelr   = PreLens { preLens = \x     -> ((x,()),       (\(x,_) -> x)) }
  ga_assoc       = PreLens { preLens = \((x,y),z) -> ( (x,(y,z)) , (\(x,(y,z)) -> ((x,y),z)) ) }
  ga_unassoc     = PreLens { preLens = \(x,(y,z)) -> ( ((x,y),z) , (\((x,y),z) -> (x,(y,z))) ) }

instance GArrowDrop PreLens (,) where
  ga_drop        = PreLens { preLens = \x     -> (()    , (\() -> x)) }
instance GArrowCopy PreLens (,) where
  ga_copy        = PreLens { preLens = \x     -> ((x,x) , fst) }
instance GArrowSwap PreLens (,) where
  ga_swap        = PreLens { preLens = \(x,y) -> ((y,x) , (\(z,q) -> (q,z))) }



data Lens x y where
  Lens :: forall x y c1 c2 . ((x,c1)->(y,c2)) -> ((y,c2)->(x,c1)) -> Lens x y

-- can we make lenses out of GArrows other than (->)?
instance Category Lens where
  id                          = Lens (\x -> x) (\x -> x)
  (Lens g1 g2) . (Lens f1 f2) = Lens (\(x,(c1,c2)) -> let (y,fc) = f1 (x,c1) in  let (z,gc) = g1 (y,c2) in  (z,(fc,gc)))
                                     (\(z,(c1,c2)) -> let (y,gc) = g2 (z,c2) in  let (x,fc) = f2 (y,c1) in  (x,(fc,gc)))

instance GArrow Lens (,) where
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

instance GArrowDrop Lens (,) where
  ga_drop        = Lens (\(x,()) -> ((),x)) (\((),x) -> (x,()))
instance GArrowCopy Lens (,) where
  ga_copy        = Lens (\(x,()) -> ((x,x),())) (\((x,_),()) -> (x,()))
instance GArrowSwap Lens (,) where
  ga_swap        = Lens (\((x,y),()) -> ((y,x),())) (\((x,y),()) -> ((y,x),()))

instance BiGArrow Lens (,) where
  biga_arr f f'  = Lens (\(x,()) -> ((f x),())) (\(x,()) -> ((f' x),()))
  biga_inv (Lens f1 f2) = Lens f2 f1
-}



--------------------------------------------------------------------------------
-- An example generalized arrow

--  *** this will be finished and posted by 14-Mar-2011; the code
--  *** below is just a sketch ***

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





{-
lambda calculus interpreter

data Val =
  Num Int
| Fun <[Val -> Val]>

This requires higher-order functions in the second level...

eval :: Exp -> a Env Val
eval (Var s)        = <[ lookup s ]>
eval (Add e1 e2)    = <[ let (Num v1) = ~(eval e1)
                      in let (Num v2) = ~(eval e2)
                      in (Num (v1+v2)) ]>
eval (If  e1 e2 e3) = <[ let v1 = ~(eval e1) in
                      in if v1
                         then ~(eval e2)
                         else ~(eval e3) ]>
eval (Lam x  e)     = ???

eval (Var s) = proc env ->
                returnA -< fromJust (lookup s env)
eval (Add e1 e2) = proc env ->
                (eval e1 -< env) `bind` \ ~(Num u) ->
                (eval e2 -< env) `bind` \ ~(Num v) ->
                returnA -< Num (u + v)
eval (If e1 e2 e3) = proc env ->
                (eval e1 -< env) `bind` \ ~(Bl b) ->
                if b    then eval e2 -< env
                        else eval e3 -< env
eval (Lam x e) = proc env ->
                returnA -< Fun (proc v -> eval e -< (x,v):env)
eval (App e1 e2) = proc env ->
                (eval e1 -< env) `bind` \ ~(Fun f) ->
                (eval e2 -< env) `bind` \ v ->
                f -< v

eval (Var s)       = <[ \env -> fromJust (lookup s env)             ]>
eval (Add e1 e2)   = <[ \env -> (~(eval e1) env) + (~(eval e2) env) ]>
eval (If e1 e2 e3) = <[ \env -> if   ~(eval e1) env
                                then ~(eval e2) env
                                else ~(eval e2) env
eval (Lam x e)     = <[ \env -> Fun (\v -> ~(eval e) ((x,v):env)) ]>
eval (App e1 e2)   = <[ \env -> case ~(eval e1) env of
                                   (Fun f) -> f (~(eval e2) env) ]>
eval (Var s)     <[env]> = <[ fromJust (lookup s env)             ]>
eval (Add e1 e2) <[env]> = <[ (~(eval e1) env) + (~(eval e2) env) ]>
-}





{-
immutable heap with cycles

-- an immutable heap; maps Int->(Int,Int)

alloc  :: A (Int,Int) Int
lookup :: A Int       (Int,Int)

onetwocycle :: A (Int,Int) (Int,Int)
onetwocycle =
  proc \(x,y)-> do
                 x' <- alloc -< (1,y)
                 y' <- alloc -< (2,x)
                 return (x',y')
\end{verbatim}

\begin{verbatim}
alloc  :: <[ (Int,Int) ->  Int      ]>
lookup :: <[ Int       -> (Int,Int) ]>

onetwocycle :: <[ (Int,Int) ]> -> <[ (Int,Int) ]>
onetwocycle x y = <[
  let    x' = ~alloc (1,~y)
  in let y' = ~alloc (2,~x)
  in (x',y')
]>

onetwocycle' :: <[ (Int,Int) -> (Int,Int) ]>
onetwocycle' = back2 onetwocycle
\end{verbatim}
-}




{-
The example may seem a little contrived, but its purpose is to
illustrate the be- haviour when the argument of mapC refers both to
its parameter and a free vari- able (n).

\begin{verbatim}
-- we can use mapA rather than mapC (from page 100)

mapA f = proc xs -> case xs of
[] -> returnA -< [] x:xs’ -> do y <- f -< x
ys’ <- mapA f -< xs’ returnA -< y:ys

example2 =
   <[ \(n,xs) -> 
       ~(mapA <[ \x-> (~(delay 0) n, x) ]> )
        xs
    ]>

<[ example2 (n,xs) =
   ~(mapA <[ \x-> (~(delay 0) n, x) ]> ) xs ]>
\end{verbatim}
-}






{-
delaysA =
   arr listcase >>>
    arr (const []) |||
     (arr id *** (delaysA >>> delay []) >>>
       arr (uncurry (:)))

nor :: SF (Bool,Bool) Bool
nor = arr (not.uncurry (||))

edge :: SF Bool Bool
edge =
   proc a -> do
   b <- delay False -< a
   returnA -< a && not b

flipflop =
   proc (reset,set) -> do
   rec c <- delay False -< nor
   reset d d <- delay True -< nor set c
   returnA -< (c,d)

halfAdd :: Arrow arr => arr (Bool,Bool) (Bool,Bool)
halfAdd =
   proc (x,y) -> returnA -< (x&&y, x/=y)

fullAdd ::
   Arrow arr => arr (Bool,Bool,Bool) (Bool,Bool)
fullAdd =
   proc (x,y,c) -> do
   (c1,s1) <- halfAdd -< (x,y)
   (c2,s2) <- halfAdd -< (s1,c)
   returnA -< (c1||c2,s2)

Here is the appendix of Hughes04:
module Circuits where
import Control.Arrow import List
class ArrowLoop a => ArrowCircuit a where delay :: b -> a b b
nor :: Arrow a => a (Bool,Bool) Bool nor = arr (not.uncurry (||))
flipflop :: ArrowCircuit a => a (Bool,Bool) (Bool,Bool) flipflop = loop (arr (\((a,b),~(c,d)) -> ((a,d),(b,c))) >>>
nor *** nor >>> delay (False,True) >>> arr id &&& arr id)
class Signal a where showSignal :: [a] -> String
instance Signal Bool where showSignal bs = concat top++"\n"++concat bot++"\n"
where (top,bot) = unzip (zipWith sh (False:bs) bs) sh True True = ("__"," ") sh True False = (" ","|_") sh False True = (" _","| ")
sh False False = (" ","__")
instance (Signal a,Signal b) => Signal showSignal xys = showSignal (map fst showSignal (map snd
instance Signal a => Signal [a] where showSignal = concat . map showSignal
sig = concat . map (uncurry replicate)
(a,b) where xys) ++ xys)
. transpose
flipflopInput = sig [(5,(False,False)),(2,(False,True)),(5,(False,False)),
(2,(True,False)),(5,(False,False)),(2,(True,True)), (6,(False,False))]





-- from Hughes' "programming with Arrows"

mapC :: ArrowChoice arr => arr (env,a) b -> arr (env,[a]) [b] mapC c = proc (env,xs) ->
case xs of [] -> returnA -< [] x:xs’ -> do y <- c -< (env,x)
ys <- mapC c -< (env,xs’) returnA -< y:ys

example2 = proc (n,xs) -> (| mapC (\x-> do delay 0 -< n
&&& do returnA -< x) |) xs
-}



