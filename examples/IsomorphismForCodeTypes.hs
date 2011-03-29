{-# OPTIONS_GHC -XModalTypes -ddump-types -XNoMonoPatBinds #-}
module IsomorphismForCodeTypes
where

--------------------------------------------------------------------------------
-- Taha-Sheard "isomorphism for code types"

back  :: forall a b c. (<[b]>@a -> <[c]>@a) -> <[ b->c ]>@a
back  = \f -> <[ \x -> ~~(f <[x]>) ]>

forth :: forall a b c. <[b->c]>@a -> (<[b]>@a -> <[c]>@a)
forth = \f -> \x -> <[ ~~f ~~x ]>
