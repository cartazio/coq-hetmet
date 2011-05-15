{-# OPTIONS_GHC -XRankNTypes -XScopedTypeVariables -XFlexibleContexts -XModalTypes -XKindSignatures -fcoqpass -XMultiParamTypeClasses -dcore-lint #-}
module Demo (foo) where
import GHC.HetMet.GArrow
import GHC.HetMet.CodeTypes
import GHC.HetMet.Private
--import GArrowTikZ

{-
foo :: (forall g a . <[ () -> a
                 PGArrow g (GArrowUnit g) a ->
                 (forall b . PGArrow g (GArrowTensor g b b) b) ->
-}
--foo con mer   = <[ ~~mer ~~con ~~con ]>
foo const merge = <[ ~~merge ~~const (~~merge ~~const ~~const) ]>

--tester2 f = <[ \x -> ~~f x x ]>

--main = tikz' $ \a b -> pga_flatten (foo (pga_unflatten a))
