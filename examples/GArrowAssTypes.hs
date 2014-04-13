{-# LANGUAGE RankNTypes, FlexibleContexts, NoMonomorphismRestriction, ScopedTypeVariables #-}
--
-- |
-- Module      :  GArrowAssTypes
-- Copyright   :  none
-- License     :  public domain
--
-- Maintainer  :  Adam Megacz <megacz@acm.org>
-- Stability   :  experimental
--
-- | This module is a gigantic type inference hack; it redefines all of the
--   ga_functions with a slightly more specific type whereby each type g
--   which is a GArrow instance also has an *associated type* (GArrowTensor g)
--   for its tensor and (GArrowUnit g) for its unit.
--
--   DO import this module without qualification if you plan on
--   writing GArrow-expressions with as few annotations as possible.
--
--   DO NOT import this module without qualification if you plan on
--   creating new instances of GArrow.  Use "import qualified" or
--   don't import it at all.
--

module GArrowAssTypes
       (ga_copy
       ,ga_drop
       ,ga_swap
       , module Control.GArrow
       )
    where
import System.IO
import qualified Control.GArrow as G
import Control.GArrow hiding (ga_copy, ga_drop, ga_swap)

{-
ga_copy :: forall x . forall g . GArrowCopy g (GArrowTensor g) (GArrowUnit g) => g x (GArrowTensor g x x)
ga_copy = G.ga_copy

ga_drop :: forall x . forall g . GArrowDrop g (GArrowTensor g) (GArrowUnit g) => g x (GArrowUnit g)
ga_drop = G.ga_drop

ga_swap :: forall x y . forall g . GArrowSwap g (GArrowTensor g) (GArrowUnit g) => g (GArrowTensor g x y) (GArrowTensor g y x)
ga_swap = G.ga_swap
-}


ga_copy :: forall x . forall g . GArrowCopy g (,) () => g x ((,) x x)
ga_copy = G.ga_copy

ga_drop :: forall x . forall g . GArrowDrop g (,) () => g x ()
ga_drop = G.ga_drop

ga_swap :: forall x y . forall g . GArrowSwap g (,) () => g ((,) x y) ((,) y x)
ga_swap = G.ga_swap



