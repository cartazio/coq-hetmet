{-# OPTIONS_GHC -XModalTypes -fflatten -funsafe-skolemize -dcore-lint -XScopedTypeVariables #-}
module Demo (demo) where


demo const mult = <[ \(y::Int) -> ~~mult y ~~(const 12) ]>
{-
demo const mult = <[ \y -> ~~(demo' 0) ]>
  where
   demo' 0 = const 4
   demo' n = const 4
-}
-- demo' n = <[ ~~mult ~~(demo' (n-1)) ~~(demo' (n-1)) ]>



{-
demo const mult =
   <[ \y -> let y = ~~(const 4) in ~~mult (~~mult y y) (~~mult y y) ]>
-}

{-
demo const mult =
   <[ \(y::Int) ->
      let four   = ~~mult four ~~(const  4)
--          twelve = {- {- ~~mult four -}  ~~(const 12) -} four
      in  four
    ]>
-}
demo ::
    forall c . 
         (Int -> <[Int]>@c) -> 
        <[Int -> Int -> Int]>@c ->
        <[Int -> Int]>@c

{-
demo const mult =
 <[ let     twelve = ~~(const (12::Int))
    in let  four    = ~~(const (4::Int))
         in  ~~mult four twelve  ]>
-}
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