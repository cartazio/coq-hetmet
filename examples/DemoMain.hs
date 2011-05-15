{-# OPTIONS_GHC -dcore-lint #-}
import Control.Category
import GHC.HetMet.GArrow
import GHC.HetMet.CodeTypes
import GHC.HetMet.Private
import GArrowTikZ
import Demo

main = tikz' $ \const merge -> foo const (pga_comp (pga_second pga_cancelr) merge)
