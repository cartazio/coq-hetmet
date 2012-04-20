{-# LANGUAGE FunctionalDependencies, NoMonomorphismRestriction, MultiParamTypeClasses #-}
module GArrowShow(GArrowShow) where
import Control.GArrow

class GArrow g (**) u => GArrowShow g (**) u where
  ga_show :: g x y -> String
