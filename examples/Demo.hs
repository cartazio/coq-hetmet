{-# OPTIONS_GHC -XModalTypes -fflatten -funsafe-skolemize -dcore-lint -XScopedTypeVariables -fsimpleopt-before-flatten #-}
module Demo (demo) where

{-
demo const mult =
  <{ \y ->
     ~~mult
       (~~mult y y)
       (~~mult y y)
   }>
-}






{-
demo const mult =
  <{ \y ->
     ~~mult
       (~~mult (~~mult y y) (~~mult y y))
       (~~mult (~~mult y y) (~~mult y y))
   }>
-}



{-
demo const mult =
    <{ \y -> ~~(foo 4) }>
        where
          foo 0 = const (12::Int)
          foo n = <{ let bar = ~~(foo (n-1))
                     in ~~mult bar bar
                   }>

-}



{-
demo const mult =
    <{ \y -> ~~(foo 3) }>
        where
          foo 0 = const (12::Int)
          foo n = <{ let recurs = ~~(foo (n-1))
                     in  ~~mult recurs recurs
                   }>

-}





demo const mult =
 <{ \y ->
    let   foo  = ~~mult (~~mult foo (~~mult y foo)) y
    in    foo }>












{-
demo const mult =
    <{ \y -> ~~(foo 2 <{y}>) }>
        where
          foo 0 y = const (12::Int)
          foo n y = <{ let recurs = ~~(foo (n-1) y)
                       in  ~~mult recurs recurs
                     }>
-}









































-- demo const mult = <{ \(y::Int) -> ~~mult y ~~(const 12) }>
-- demo' n = <{ ~~mult ~~(demo' (n-1)) ~~(demo' (n-1)) }>
-- golden
{-
demo const mult =
 <{ \y ->
    let   twelve  = ~~mult twelve y
    in    twelve }>
-}

{-
demo const mult =
   <{ \y -> let y = ~~(const 4) in ~~mult (~~mult y y) (~~mult y y) }>
-}

{-
demo const mult =
   <{ \(y::Int) ->
      let four   = ~~mult four ~~(const  4)
--          twelve = {- {- ~~mult four -}  ~~(const 12) -} four
      in  four
    }>
-}
demo ::
    forall c . 
         (Int -> <{Int}>@c) -> 
        <{Int -> Int -> Int}>@c ->
        <{Int -> Int}>@c

{-
demo const mult =
 <{ let     twelve = ~~(const (12::Int))
    in let  four    = ~~(const (4::Int))
         in  ~~mult four twelve  }>
-}

{-
demo const mult = demo' 3
 where
  demo' 0 = const 12
  demo' 1 = const 12
  demo' n = <{ ~~mult ~~(demo' (n-1)) ~~(demo' (n-2)) }>
-}

-- BUG
--demo const mult = <{ \y -> ~~(demo' 0) }>
--  where
--   demo' 0 = const 4
--   demo' n = const 4
