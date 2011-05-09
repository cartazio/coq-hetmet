{-# OPTIONS_GHC -XRankNTypes -XScopedTypeVariables -XFlexibleContexts -XModalTypes -XKindSignatures -fcoqpass -XMultiParamTypeClasses -dcore-lint #-}
import GHC.HetMet.GArrow
import GHC.HetMet.CodeTypes
import GHC.HetMet.Private
import GArrowTikZ

foo x = <[ ~~x ]>
foo' = unG . pga_flatten . foo . pga_unflatten
--foo x z = <[ let y = ~~x in ~~z y y ]>
main = tikz (foo' (PGArrowD { unG = TikZ_const 12 }))
