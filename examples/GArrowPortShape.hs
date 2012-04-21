{-# LANGUAGE MultiParamTypeClasses, GADTs, FlexibleContexts, FlexibleInstances, TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  GArrowPortShape
-- Copyright   :  none
-- License     :  public domain
--
-- Maintainer  :  Adam Megacz <megacz@acm.org>
-- Stability   :  experimental
--
-- | We cannot, at run time, query to find out the input and output
-- port types of a GArrowSkeleton since Haskell erases types during
-- compilation.  Using Data.Typeable is problematic here because
-- GAS_comp and GAS_loop{l,r} have an existential type.
--
-- In spite of this, we can determine the "shape" of the ports --
-- which ports are of unit type, and which ports must be tensors.  A
-- GArrowPortShape is a GArrowSkeleton along with this
-- information for certain nodes (the inference mechanism below adds
-- it on every node).
--
module GArrowPortShape (GArrowPortShape(..), PortShape(..), detectShape, Detect(..), DetectM, freshM)
where
import Prelude hiding ( id, (.), lookup )
import Control.Category
import Control.GArrow
import Unify
import GArrowSkeleton
import Control.Monad.State

--
-- | Please keep in mind that the "shapes" computed below are simply the
-- least-complicated shapes that could possibly work.  Just because a
-- GArrowPortShape has an input port of shape (x,y)
-- doesn't mean it couldn't later be used in a context where its input
-- port had shape ((a,b),y)!  However, you can be assured that it
-- won't be used in a context where the input port has shape ().
--
data PortShape a = PortUnit
                 | PortTensor (PortShape a) (PortShape a)
                 | PortFree a

instance Show a => Show (PortShape a) where
 show PortUnit           = "U"
 show (PortTensor p1 p2) = "("++show p1++"*"++show p2++")"
 show (PortFree x)       = show x

data GArrowPortShape m s a b =
    GASPortPassthrough
      (PortShape s)
      (PortShape s)
      (m a b)
  | GASPortShapeWrapper
      (PortShape s)
      (PortShape s)
      (GArrowSkeleton (GArrowPortShape m s) a b)

--
-- implementation below; none of this is exported
--

type UPort = PortShape UVar

instance Unifiable UPort where
  unify' (PortTensor x1 y1) (PortTensor x2 y2) = mergeU (unify x1 x2) (unify y1 y2)
  unify' PortUnit PortUnit                     = emptyUnifier
  unify' s1 s2                                 = error $ "Unifiable UPort got impossible unification case: "

  replace uv prep PortUnit                    = PortUnit
  replace uv prep (PortTensor p1 p2)          = PortTensor (replace uv prep p1) (replace uv prep p2)
  replace uv prep (PortFree x)                = if x==uv then prep else PortFree x

  inject                                       = PortFree
  project (PortFree v)                         = Just v
  project _                                    = Nothing
  occurrences (PortFree v)                     = [v]
  occurrences (PortTensor x y)                 = occurrences x ++ occurrences y
  occurrences PortUnit                         = []

-- detection monad
type DetectM a = State ((Unifier UPort),[UVar]) a

shapes :: GArrowPortShape m UVar a b -> (UPort,UPort)
shapes (GASPortPassthrough  x y _) = (x,y)
shapes (GASPortShapeWrapper x y _) = (x,y)

unifyM :: UPort -> UPort -> DetectM ()
unifyM p1 p2 = do { (u,vars) <- get
                  ; put (mergeU u $ unify p1 p2 , vars)
                  }

freshM :: DetectM UVar
freshM = do { (u,(v:vars)) <- get
            ; put (u,vars)
            ; return v
            }

-- recursive version of getU
getU' :: Unifier UPort -> UPort -> PortShape ()
getU' u (PortTensor x y)  = PortTensor (getU' u x) (getU' u y)
getU' _ PortUnit          = PortUnit
getU' u x@(PortFree v)    = case Unify.getU u v  of
                                     Nothing -> PortFree () -- or x
                                     Just x' -> getU' u x'

resolveG :: Unifier UPort -> (GArrowPortShape m UVar a b) -> GArrowPortShape m () a b
resolveG u (GASPortPassthrough  x y m) = GASPortPassthrough  (getU' u x) (getU' u y) m
resolveG u (GASPortShapeWrapper x y g) = GASPortShapeWrapper (getU' u x) (getU' u y) (resolveG' g)
 where
  resolveG' :: GArrowSkeleton (GArrowPortShape m UVar)             a b -> 
               GArrowSkeleton (GArrowPortShape m ())   a b
  resolveG' (GAS_id           ) = GAS_id
  resolveG' (GAS_comp      f g) = GAS_comp (resolveG' f) (resolveG' g)
  resolveG' (GAS_first       f) = GAS_first (resolveG' f)
  resolveG' (GAS_second      f) = GAS_second (resolveG' f)
  resolveG' GAS_cancell         = GAS_cancell
  resolveG' GAS_cancelr         = GAS_cancelr
  resolveG' GAS_uncancell       = GAS_uncancell
  resolveG' GAS_uncancelr       = GAS_uncancelr
  resolveG' GAS_drop            = GAS_drop
  resolveG' GAS_copy            = GAS_copy
  resolveG' GAS_swap            = GAS_swap
  resolveG' GAS_assoc           = GAS_assoc
  resolveG' GAS_unassoc         = GAS_unassoc
  resolveG' (GAS_loopl f)       = GAS_loopl (resolveG' f)
  resolveG' (GAS_loopr f)       = GAS_loopr (resolveG' f)
  resolveG' (GAS_misc g )       = GAS_misc $ resolveG u g

detectShape :: Detect m => GArrowSkeleton m a b -> GArrowPortShape m () a b
detectShape g = runM (detect g)

runM :: Detect m => DetectM (GArrowPortShape m UVar a b) -> GArrowPortShape m () a b
runM f = let s     = (emptyUnifier,uvarSupply)
             g     = evalState f s
             (u,_) = execState f s
          in resolveG u g

class Detect m where
  detect' :: m x y -> DetectM (GArrowPortShape m UVar x y)

detect :: Detect m => GArrowSkeleton m a b -> DetectM (GArrowPortShape m UVar a b)
detect (GAS_id      ) = do { x <- freshM ; return $ GASPortShapeWrapper (PortFree x) (PortFree x) GAS_id }
detect (GAS_comp f g) = do { f' <- detect f
                           ; g' <- detect g
                           ; unifyM (snd $ shapes f') (fst $ shapes g')
                           ; return $ GASPortShapeWrapper (fst $ shapes f') (snd $ shapes g') (GAS_comp (GAS_misc f') (GAS_misc g'))
                           }
detect (GAS_first  f) = do { x <- freshM
                           ; f' <- detect f
                           ; return $ GASPortShapeWrapper
                                        (PortTensor (fst $ shapes f') (PortFree x))
                                        (PortTensor (snd $ shapes f') (PortFree x))
                                        (GAS_first (GAS_misc f'))
                           }
detect (GAS_second f) = do { x <- freshM
                           ; f' <- detect f
                           ; return $ GASPortShapeWrapper
                                        (PortTensor (PortFree x) (fst $ shapes f'))
                                        (PortTensor (PortFree x) (snd $ shapes f'))
                                        (GAS_second (GAS_misc f'))
                           }
detect GAS_cancell    = do { x <- freshM; return$GASPortShapeWrapper (PortTensor PortUnit (PortFree x)) (PortFree x) GAS_cancell }
detect GAS_cancelr    = do { x <- freshM; return$GASPortShapeWrapper (PortTensor (PortFree x) PortUnit) (PortFree x) GAS_cancelr }
detect GAS_uncancell  = do { x <- freshM; return$GASPortShapeWrapper (PortFree x) (PortTensor PortUnit (PortFree x)) GAS_uncancell }
detect GAS_uncancelr  = do { x <- freshM; return$GASPortShapeWrapper (PortFree x) (PortTensor (PortFree x) PortUnit) GAS_uncancelr }
detect GAS_drop       = do { x <- freshM; return$GASPortShapeWrapper (PortFree x) PortUnit GAS_drop }
detect GAS_copy       = do { x <- freshM
                           ; return $ GASPortShapeWrapper (PortFree x) (PortTensor (PortFree x) (PortFree x)) GAS_copy }
detect GAS_swap       = do { x <- freshM
                           ; y <- freshM
                           ; let x' = PortFree x
                           ; let y' = PortFree y
                           ; return $ GASPortShapeWrapper (PortTensor x' y') (PortTensor y' x') GAS_swap
                           }
detect GAS_assoc      = do { x <- freshM; y <- freshM; z <- freshM
                           ; let x' = PortFree x
                           ; let y' = PortFree y
                           ; let z' = PortFree z
                           ; return $ GASPortShapeWrapper
                                        (PortTensor (PortTensor x' y') z')
                                        (PortTensor x' (PortTensor y' z'))
                                        GAS_assoc
                           }
detect GAS_unassoc    = do { x <- freshM; y <- freshM; z <- freshM
                           ; let x' = PortFree x
                           ; let y' = PortFree y
                           ; let z' = PortFree z
                           ; return $ GASPortShapeWrapper
                                        (PortTensor x' (PortTensor y' z'))
                                        (PortTensor (PortTensor x' y') z')
                                        GAS_unassoc
                           }
detect (GAS_loopl f)  = do { x <- freshM
                           ; y <- freshM
                           ; z <- freshM
                           ; f' <- detect f
                           ; unifyM (fst $ shapes f') (PortTensor (PortFree z) (PortFree x))
                           ; unifyM (snd $ shapes f') (PortTensor (PortFree z) (PortFree y))
                           ; return $ GASPortShapeWrapper (PortFree x) (PortFree y) (GAS_loopl (GAS_misc f'))
                           }
detect (GAS_loopr f)  = do { x <- freshM
                           ; y <- freshM
                           ; z <- freshM
                           ; f' <- detect f
                           ; unifyM (fst $ shapes f') (PortTensor (PortFree x) (PortFree z))
                           ; unifyM (snd $ shapes f') (PortTensor (PortFree y) (PortFree z))
                           ; return $ GASPortShapeWrapper (PortFree x) (PortFree y) (GAS_loopr (GAS_misc f'))
                           }

detect (GAS_misc f)   = detect' f

