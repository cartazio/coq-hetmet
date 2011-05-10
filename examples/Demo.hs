{-# OPTIONS_GHC -XRankNTypes -XScopedTypeVariables -XFlexibleContexts -XModalTypes -XKindSignatures -fcoqpass -XMultiParamTypeClasses -dcore-lint #-}
import GHC.HetMet.GArrow
import GHC.HetMet.CodeTypes
import GHC.HetMet.Private
import GArrowTikZ

foo x = <[ ~~x ]>

main = tikz' $ pga_flatten . foo . pga_unflatten
