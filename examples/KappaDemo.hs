{-# OPTIONS_GHC -XModalTypes -dcore-lint -XScopedTypeVariables -ddump-types #-}
module Demo (demo, demo2) where

demo  z   = <{ \y -> ~~z }>

demo2 :: <[ (a,b) ~~> c ]>@d -> <[ () ~~> a ]>@d -> <[ b ~~>c ]>@d
demo2 x y = <{ ~~x ~~y }>

demo3 x y z q = <{ ~~q (~~x ~~y ~~z) }>



