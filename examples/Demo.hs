{-# OPTIONS_GHC -XModalTypes -fcoqpass -dcore-lint #-}
module Demo (demo) where

--demo con mer = <[ ~~mer ~~(con (2::Int)) ~~(con (12::Int)) ]>

-- demo const mult = <[ let q = ~~(const (1::Int)) in ~~mult q q ]>

demo const mult =
 <[ let     twelve = ~~(const (12::Int))
    in let  four    = ~~(const (4::Int))
         in  ~~mult four twelve  ]>

{-
demo const mult =
 <[ let     twelve = ~~(const (12::Int))
    in let  twelvea = twelve
            four    = ~~(const (4::Int))
            twelveb = twelve
         in  ~~mult (~~mult twelvea four) (~~mult twelveb twelveb) ]>
-}

{-
demo const mult = demo' 3
 where
  demo' 0 = const 12
  demo' 1 = const 12
  demo' n = <[ ~~mult ~~(demo' (n-1)) ~~(demo' (n-2)) ]>
-}