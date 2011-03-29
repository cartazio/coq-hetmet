{-# OPTIONS_GHC -XModalTypes -XScopedTypeVariables -ddump-types -XNoMonoPatBinds #-}
module ImmutableHeap
where
import IsomorphismForCodeTypes
import Prelude hiding ( id, (.) )

class GuestLanguageHeap c where
  alloc  :: <[ (Integer,Integer) ->  Integer      ]>@c
  lookup :: <[ Integer       -> (Integer,Integer) ]>@c

onetwocycle = back onetwocycle'
 where
  onetwocycle' xy = <[ let (x,y) = ~~xy 
                       in let x' = ~~alloc (1,x)
                       in let y' = ~~alloc (2,y)
                       in (x',y')
                     ]>
