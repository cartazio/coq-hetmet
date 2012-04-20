{-# LANGUAGE FunctionalDependencies, NoMonomorphismRestriction, MultiParamTypeClasses #-}
module GArrowInclusion(GArrowInclusion(ga_inc)) where
import Control.GArrow

class GArrow g (**) u => GArrowInclusion g (**) u g' where
  ga_inc :: g' x y -> g x y
