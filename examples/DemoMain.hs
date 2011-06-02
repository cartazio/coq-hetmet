import Control.Category
import GArrowTikZ
import GHC.HetMet.Private
import GHC.HetMet.GArrow
import Demo

{-
demo' ::
         (Int -> PGArrow g (GArrowUnit g) (GArrowTensor g (GArrowUnit g) Int) ) -> 
         (       PGArrow g (GArrowTensor g (GArrowTensor g Int Int) (GArrowUnit g)) Int) ->
         (PGArrow g (GArrowUnit g) (GArrowTensor g (GArrowUnit g) Int) )
demo' = demo
-}

main = tikz $ \const merge -> demo const merge
