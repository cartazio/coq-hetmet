{-# OPTIONS_GHC -XModalTypes -fcoqpass -dcore-lint #-}
module Demo (demo) where

demo con mer = <[ ~~mer ~~(con (2::Int)) ~~(con (12::Int)) ]>

-- demo const mult = <[ let q = ~~(const (1::Int)) in ~~mult q q ]>

--demo const mult =
-- <[ let twelve = ~~(const (12::Int))
--    in  ~~mult (~~mult twelve twelve) (~~mult twelve twelve) ]>

{-
demo const mult = demo' 3
 where
  demo' 0 = const 12
  demo' 1 = const 12
  demo' n = <[ ~~mult ~~(demo' (n-1)) ~~(demo' (n-2)) ]>
-}