{-# OPTIONS_GHC -XModalTypes -dcore-lint -XScopedTypeVariables -ddump-types -XTypeFamilies -XNoMonomorphismRestriction #-}
module Demo (demo, demo2) where

demo  z   = <{ \y -> ~~z }>

demo2 :: <[ (a,b) ~~> c ]>@d -> <[ () ~~> a ]>@d -> <[ b ~~>c ]>@d
demo2 x y = <{ ~~x ~~y }>

swap :: <[ (a,(b,c)) ~~> d ]>@e -> <[ (b,(a,c)) ~~> d ]>@e
swap f = <{ \x -> \y -> ~~f y x }>

-- bad = <{ \f -> \x -> f x }>

demo3 x y z q = <{ ~~q (~~x ~~y ~~z) }>



class BitSerialHardwarePrimitives g where
  type Wire

  <[ not ]>    :: <[             (Wire,())    ~~> Wire ]>@g
  <[ xor ]>    :: <[       (Wire,(Wire,()))   ~~> Wire ]>@g
  <[ or  ]>    :: <[       (Wire,(Wire,()))   ~~> Wire ]>@g
  <[ and ]>    :: <[       (Wire,(Wire,()))   ~~> Wire ]>@g
  <[ mux2 ]>   :: <[ (Wire,(Wire,(Wire,())))  ~~> Wire ]>@g
  <[ maj3 ]>   :: <[ (Wire,(Wire,(Wire,())))  ~~> Wire ]>@g
  <[ reg ]>    :: <[             (Wire,())    ~~> Wire ]>@g
  <[ zero ]>   :: <[             ()    ~~> Wire ]>@g
  <[ one ]>    :: <[             ()    ~~> Wire ]>@g

  loop   :: [Bool] -> <[ () ~~> Wire ]>@g
  <[ lfsr ]>   :: Int ->  [ <[ Wire ]>@g ]
  <[ adder ]>  :: <[  (Wire,(Wire,())) ~~> Wire ]>@g
  fifo         :: Int -> <[  (Wire,()) ~~> Wire ]>@g

  <[ probe ]>  :: Int -> <[ (Wire,())  ~~> Wire ]>@g
  <[ oracle ]> :: Int -> <[                Wire ]>@g

xor3 :: forall g . BitSerialHardwarePrimitives g => <[ (Wire,(Wire,(Wire,()))) ~~> Wire ]>@g
xor3 = <{ \x -> \y -> \z -> xor (xor x y) z }>

adder =
   <{ \in1 ->
      \in2 ->
      let firstBitMarker = ~~(loop [ i/=0 | i <- [0..31] ])
          carry_out      = reg (mux2 firstBitMarker zero carry_in)
          carry_in       = maj3 carry_out in1 in2
      in  ~~xor3 carry_out in1 in2
    }>


rotRight n =
  <{ \input ->
     let sel   = ~~(loop [ i >= 32-n | i<-[0..31] ])
         fifo1 = ~~(fifo (32-n)) input
         fifo2 = ~~(fifo  32   ) fifo1
     in  mux2 sel fifo1 fifo2
   }>

sha256round =
  <{ \load ->
     \input ->
     \k_plus_w ->
     let a    = ~~(fifo 32) (mux2 load a_in input)
         b    = ~~(fifo 32) a
         c    = ~~(fifo 32) b
         d    = ~~(fifo 32) c
         e    = ~~(fifo 32) (mux2 load e_in d)
         f    = ~~(fifo 32) e
         g    = ~~(fifo 32) f
         h    = ~~(fifo 32) g
         s0   = ~~xor3
                    (~~(rotRight  2) a_in)
                    (~~(rotRight 13) a_in)
                    (~~(rotRight 22) a_in)
         s1   = ~~xor3
                    (~~(rotRight  6) e_in)
                    (~~(rotRight 11) e_in)
                    (~~(rotRight 25) e_in)
         a_in = adder t1 t2
         e_in = adder t1 d
         t1   = adder
                   (adder h s1)
                   (adder (mux2 e g f)
                          k_plus_w)
         t2   = adder s0 (maj3 a b c)
     in h
   }>