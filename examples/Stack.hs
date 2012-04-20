{-# OPTIONS_GHC -XModalTypes -dcore-lint -ddump-types -XNoMonomorphismRestriction #-}
module Stack where
import Prelude hiding (const)

class ProcessNetwork g where
  logic   :: (        Bool -> Bool) -> <[       Bool  ~~> Bool ]>
  logic2  :: (Bool -> Bool -> Bool) -> <[ (Bool,Bool) ~~> Bool ]>
  delay   ::                  Bool  -> <[       Bool  ~~> Bool ]>
  select  :: <[ (Bool,Bool,Bool)  ~~>       Bool  ]>
  switch  :: <[ (Bool,Bool)       ~~> (Bool,Bool) ]>

------------------------------------------------------------------------------
--
-- Basic logic functions
--
and' = logic2 (\x y -> x && y)
or'  = logic2 (\x y  -> x || y)
not' = logic  (\x -> case x of {True->False ; False -> True})

--
-- Simulates "conditionally consuming" data from an input port.
--
-- A value is consumed from "next"; if the value is False,
-- the previous output is repeated.  Otherwise, a value is
-- consumed from "input" and emitted as the output.
--
--peek :: <[ (Bool,Bool) ~~> Bool ]>
peek input next = 
  <[ \input ->
     \next ->
     let
       prev         = ~~(delay True) next
       out          = select prev input feedback
--     (feedback,_) = switch next out
       feedback     = switch' next out
     in out
   ]>


------------------------------------------------------------------------------
--
-- Numbers are represented in unary (Peano) notation: the number N is
-- N-many False values followed by a single True
--
type Number = Bool


--
-- Convert a Number to a sequence of False's; the second argument
-- is a stream of Bools, one per Number, indicating whether or not
-- to include the trailing "True"
--
--numberToBooleans :: <[ (Number,Bool) ~~> Bool ]>
allTrues :: forall g . <[ () ~~> Bool ]>@g
allTrues = undefined
allFalses :: forall g . <[ () ~~> Bool ]>@g
allFalses = undefined

numberToBooleans =
 <[ \numbers ->
    \includeTrailingTrue ->
      let sel            = select numbers includeTrailingTrue ~~allTrues
--          (out,_)        = switch sel numbers
          out        = switch' sel numbers
      in out
  ]>


------------------------------------------------------------------------------
--
-- Increment, decrement, and zero-test for Numbers.  Each of these
-- follows a similar pattern: keep a copy of the previous input, and
-- "pattern match" on a pair of consecutive bits.
--
--decrement :: <[ Number ~~> Number ]>
decrement =
 <[ \input ->
      let isFirstBitOfNumber        = ~~(delay True) input
          isFirstBitOfNonzeroNumber = ~~and' (~~not' input) isFirstBitOfNumber
--          (_,out)                   = switch isFirstBitOfNonzeroNumber input
          out                   = switch' isFirstBitOfNonzeroNumber input
       in out
  ]>

--increment :: <[ Number ~~> Number ]>
increment =
  <[ \input ->
       let isFirstBitOfNumber = ~~(delay True) out
           out                = select isFirstBitOfNumber ~~allFalses input
        in out
   ]>
      
--isZero :: <[ Number ~~> Bool ]>
isZero =
  <[ \input ->
        let prev    = ~~(delay True) input
--          (out,_) = switch input (~~and' prev input)
            out = switch' input (~~and' prev input)
         in out
   ]>


------------------------------------------------------------------------------
--
-- Versions of the "select" and "select" operators that act on Numbers
-- (the "select" port is still boolean).
--
-- numberSelect :: <[ (Bool,Number,Number) ~~> Number ]>
{-
numberSelect =
  <[ \sel ->
     \iftrue ->
     \iffalse ->
        let sel'     = ~~peek sel next_sel
            out      = select sel' iftrue iffalse
            next_sel = out
        in  out
   ]>
-}

numberSwitch :: <[ (Bool,Number) ~~> (Number,Number) ]>
{-
numberSwitch =
  <[ \sel ->
     \input ->
        let sel'     = ~~peek sel next_sel
            out      = switch sel' input
            next_sel = input
        in  out
   ]>
-}

numberSelect :: <[ (Bool,(Number,(Number,()))) ~~> Number ]>@g
numberSelect = undefined

------------------------------------------------------------------------------
--
-- An example of a functional: given two process networks which each
-- take a Number in and produce a Number output, route each incoming
-- Number to one side or the other based on a control token.
--
{-
maybeNumber :: ([Number] -> [Number]) ->
              ([Number] -> [Number]) ->
              [Bool] ->
              [Number] ->
              [Number]

maybeNumber ftrue ffalse sel input = 
  let (inputTrue,inputFalse) = numberSwitch sel input
   in numberSelect sel (ftrue inputTrue) (ffalse inputFalse)
-}
maybeNumber ::
   <[ Number ~~> Number ]>@g ->
   <[ Number ~~> Number ]>@g ->
   <[ (Bool,Number) ~~> Number ]>@g
maybeNumber = undefined


------------------------------------------------------------------------------
stack =
  <[ \commandIsPop ->
     \push ->
     let 
       -- relatively straightforward: the counter, counter update, and emptiness test:
       count               = ~~(delay True) newCount
       newCount            = ~~maybeNumber ~~decrement ~~increment commandIsPop count
       isEmpty             = ~~isZero count
       pushOrPopEmpty      = ~~or' (~~not' commandIsPop) isEmpty

       -- First stage: popping from an empty stack is implemented by
       -- synthesizing a zero value, pushing it, and then popping it.
       -- This first stage synthesizes the zero-value if necessary
       (popEmptyResult,_)  = ~~numberSwitch
                               pushOrPopEmpty
                               (~~numberSelect
                                  commandIsPop
                                  ~~allTrues
                                  push)

       -- Second stage: this select copies the existing stack storage
       -- from its first input to its output, optionally *preceding* it
       -- with a single value drawn from its second input.
       pushResult          = ~~numberSelect
                                (~~numberToBooleans count pushOrPopEmpty)
                                popEmptyResult
                                stackStorage

       -- Third stage: copy the result of the "push" operation to its
       -- second output, optionally diverting the *first* element to the
       -- first output.
       (popResult,stackStorage)  = ~~numberSwitch
                                      (numberToBooleans newCount commandIsPop)
                                      pushResult
  
    in popResult
  ]>

{-

------------------------------------------------------------------------------
--
--  Boilerplate
--


int2p 0 = [True]
int2p n = False:(int2p (n-1))


p2i (True:xs)  = 0:(p2i xs)
p2i (False:xs) = case p2i xs of n:ns -> (n+1):ns
p2i _ = []

--x = peek [1,2,3,4,5,6,7,8] [True,True,False,False,True,False]
--x = p2i $ numberSelect [False,True,True,False] even odd
--x = p2i $ fst (numberSwitch [False,True,True,False,True] all)
--x = p2i $ increment even
x = p2i $ stack [True,True,False,False,False,True,True,False,True,True,True,True,True] odd
 where
   even = concatMap int2p [9,0,2,4,6]
   odd  = concatMap int2p [9,1,3,5]
   all  = concatMap int2p [1,2,0,2,3,4,9,9]

main = do sequence $ map putStrLn $ map show x

logic1 f in1     = map f in1
logic2 f in1 in2 = map f (zip in1 in2)

delay x                   = \n -> x:n

select sel iftrue iffalse =
    case sel of
      (True :sel') -> case iftrue  of { (x:iftrue')  -> x:(select sel' iftrue' iffalse)  ; _ -> [] }
      (False:sel') -> case iffalse of { (x:iffalse') -> x:(select sel' iftrue  iffalse') ; _ -> [] }
      []           -> []

switch (True:sel)  (x:inp) = let (out1,out2) = switch sel inp in ((x:out1),out2)
switch (False:sel) (x:inp) = let (out1,out2) = switch sel inp in (out1,(x:out2))
switch _ _                 = ([],[])

allTrues  = delay True  allTrues
allFalses = delay False allFalses
-}