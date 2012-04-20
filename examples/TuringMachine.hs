{-# OPTIONS_GHC -XModalTypes -dcore-lint -ddump-types -XNoMonomorphismRestriction #-}
module TuringMachine (ProcessNetwork) where
import Prelude hiding (const)

class ProcessNetwork g where
  logic         :: (Bool -> Bool -> Bool) -> <[ (Bool,(Bool,())) ~~> Bool ]>@g
  delay         :: Bool -> <[       (Bool,())  ~~> Bool ]>@g
  <[ select  ]> :: <[ (Bool,(Bool,(Bool,())))  ~~> Bool        ]>@g
  <[ switch  ]> :: <[       (Bool,(Bool,()))   ~~> (Bool,Bool) ]>@g
  <[ switch' ]> :: <[       (Bool,(Bool,()))   ~~> Bool ]>@g


or  = logic (\x y -> x || y)

not :: ProcessNetwork g => <[ (Bool,())  ~~> Bool ]>@g
not = undefined




-- every time it gets an input it spits out the same output value
const :: ProcessNetwork g => Bool -> <[ (Bool,()) ~~> Bool ]>@g
const = undefined

--
-- VERY IMPORTANT!
--
--      Bool   is the type of booleans in Haskell.
--    <[Bool]> is the type of a process network arc in which EACH TOKEN is a boolean.
--
-- This can lead to some slightly-confusing notation:
--
--    (Bool -> Bool)   is a Haskell function that takes a boolean and
--                     (if it halts) returns a Boolean.
--
--   <[Bool ~~> Bool]> is a process network with an input arc whose
--                     tokens are booleans and an output arc whose
--                     tokens are booleans
--

--
-- Think of Haskell values as being like Ptolemy model parameters!
--

condConst initVal =
   <[ \condition -> ~~(const initVal) (switch' condition condition) ]>


--
-- The size of the stack is a natural number; these will be
-- represented as a stream of values using *unary notation* in the
-- following form: the number N is represented as "true" followed by
-- N-many "false" values.
--

--
-- A UnaryNumber is just a stream that we give a particular meaning
-- to.  We're going to get some help here from Haskell's type system
-- by creating another type UnaryNumber, but not telling our code that
-- it's actually the same thing as a Stream.  This prevents us from
-- accidentally using a non-UnaryNumber stream where a UnaryNumber was
-- required!
--
type UnaryNumber = Bool


type IncDec = Bool

counter :: ProcessNetwork g => <[ IncDec ~~> UnaryNumber ]>@g
counter = undefined





-- show myself making a type error


-- Investigate later: automatic translation from <[PeanoStream~~>PeanoStream]> to <[Bool~~>Bool]>

-- show why innocuous Haskell program transforms alter the behavior of PNs