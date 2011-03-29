{-# OPTIONS_GHC -XModalTypes -XScopedTypeVariables -ddump-types -XNoMonoPatBinds #-}
module ImmutableHeap
where
import IsomorphismForCodeTypes
import Prelude hiding ( id, (.) )


class GuestLanguageHeap c where
  alloc  :: <[ (Integer,Integer) ->  Integer      ]>@c
  lookup :: <[ Integer       -> (Integer,Integer) ]>@c

--
-- Here's nice example of Sheard's observation that it's often easier
-- to write two-stage programs by applying "back" to some function rather than
-- writing the final result directly
--
onetwocycle = back onetwocycle'
 where
  onetwocycle' xy = <[ let (x,y) = ~~xy 
                       in let x' = ~~alloc (1,x)
                       in let y' = ~~alloc (2,y)
                       in (x',y')
                     ]>
