{-# LANGUAGE MultiParamTypeClasses, GADTs, FlexibleContexts, FlexibleInstances, TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  GArrowSkeleton
-- Copyright   :  none
-- License     :  public domain
--
-- Maintainer  :  Adam Megacz <megacz@acm.org>
-- Stability   :  experimental
--
-- | Sometimes it is convenient to be able to get your hands on the
-- explicit boxes-and-wires representation of a GArrow-polymorphic
-- term.  GArrowSkeleton lets you do that.
--
-- HOWEVER: technically this instance violates the laws (and RULEs)
-- for Control.Category; the compiler might choose to optimize (f >>>
-- id) into f, and this optimization would produce a change in
-- behavior below -- you'd get (GAS_comp f GAS_id) instead of f.  In
-- practice this means that the user must be prepared for the skeleton
-- TikZ diagram to be a nondeterministically-chosen boxes-and-wires
-- diagram which ks *equivalent to* the term, rather than structurally
-- exactly equal to it.
--
module GArrowSkeleton (GArrowSkeleton(..), optimize, beautify)
where
import Prelude hiding ( id, (.), lookup, repeat )
import Control.Category
import GHC.HetMet.GArrow
import Unify
import Control.Monad.State

data GArrowSkeleton m :: * -> * -> *
 where
  GAS_const     ::                                          Int -> GArrowSkeleton m () Int
  GAS_id        ::                                                 GArrowSkeleton m x x
  GAS_comp      :: GArrowSkeleton m x y -> GArrowSkeleton m y z -> GArrowSkeleton m x z
  GAS_first     :: GArrowSkeleton m x y                         -> GArrowSkeleton m (x,z)  (y,z)
  GAS_second    :: GArrowSkeleton m x y                         -> GArrowSkeleton m (z,x)  (z,y)
  GAS_cancell   ::                                                 GArrowSkeleton m ((),x) x
  GAS_cancelr   ::                                                 GArrowSkeleton m (x,()) x
  GAS_uncancell ::                                                 GArrowSkeleton m x ((),x)
  GAS_uncancelr ::                                                 GArrowSkeleton m x (x,())
  GAS_assoc     ::                                                 GArrowSkeleton m ((x,y),z) (x,(y,z))
  GAS_unassoc   ::                                                 GArrowSkeleton m (x,(y,z)) ((x,y),z)
  GAS_drop      ::                                                 GArrowSkeleton m x         ()
  GAS_copy      ::                                                 GArrowSkeleton m x         (x,x)
  GAS_swap      ::                                                 GArrowSkeleton m (x,y)     (y,x)
  GAS_merge     ::                                                 GArrowSkeleton m (x,y)     z
  GAS_loopl     ::                 GArrowSkeleton m (z,x) (z,y) -> GArrowSkeleton m x y
  GAS_loopr     ::                 GArrowSkeleton m (x,z) (y,z) -> GArrowSkeleton m x y
  GAS_misc      ::                                        m x y -> GArrowSkeleton m x y

instance Category (GArrowSkeleton m) where
  id           = GAS_id
  g . f        = GAS_comp f g

instance GArrow (GArrowSkeleton m) (,) () where
  ga_first     = GAS_first
  ga_second    = GAS_second
  ga_cancell   = GAS_cancell
  ga_cancelr   = GAS_cancelr
  ga_uncancell = GAS_uncancell
  ga_uncancelr = GAS_uncancelr
  ga_assoc     = GAS_assoc
  ga_unassoc   = GAS_unassoc

instance GArrowDrop (GArrowSkeleton m) (,) () where
  ga_drop      = GAS_drop

instance GArrowCopy (GArrowSkeleton m) (,) () where
  ga_copy      = GAS_copy

instance GArrowSwap (GArrowSkeleton m) (,) () where
  ga_swap      = GAS_swap

instance GArrowLoop (GArrowSkeleton m) (,) () where
  ga_loopl     = GAS_loopl
  ga_loopr     = GAS_loopr

type instance GArrowTensor      (GArrowSkeleton m) = (,)
type instance GArrowUnit        (GArrowSkeleton m) = ()
type instance GArrowExponent    (GArrowSkeleton m) = (->)

instance GArrowSTKCL (GArrowSkeleton m)

--
-- | Simple structural equality on skeletons.  NOTE: two skeletons
--   with the same shape but different types will nonetheless be "equal";
--   there's no way around this since types are gone at runtime.
--
instance Eq ((GArrowSkeleton m) a b)
 where
  x == y = x === y
   where
    (===) :: (GArrowSkeleton m) a b -> (GArrowSkeleton m) c d -> Bool
    (GAS_id           ) === (GAS_id           ) = True
    (GAS_comp      g f) === (GAS_comp    g' f') = f===f' && g===g'
    (GAS_first       f) === (GAS_first  f')     = f===f'
    (GAS_second      f) === (GAS_second f')     = f===f'
    GAS_cancell         === GAS_cancell         = True
    GAS_cancelr         === GAS_cancelr         = True
    GAS_uncancell       === GAS_uncancell       = True
    GAS_uncancelr       === GAS_uncancelr       = True
    GAS_drop            === GAS_drop            = True
    (GAS_const i)       === (GAS_const i')      = i==i'
    GAS_copy            === GAS_copy            = True
    GAS_merge           === GAS_merge           = True
    GAS_swap            === GAS_swap            = True
    GAS_assoc           === GAS_assoc           = True
    GAS_unassoc         === GAS_unassoc         = True
    (GAS_loopl f)       === (GAS_loopl f')      = f === f'
    (GAS_loopr f)       === (GAS_loopr f')      = f === f'
    _ === _                                     = False
    -- FIXME: GAS_misc's are never equal!!!

--
-- | Performs some very simple-minded optimizations on a
--   boxes-and-wires diagram.  Preserves equivalence up to the GArrow
--   laws, but no guarantees about which optimizations actually happen.
--
optimize :: (GArrowSkeleton m) a b -> (GArrowSkeleton m) a b
optimize = repeat (gasl2gas . optimizel . gas2gasl)

{-
optimize x = let x' = optimize' x in if x == x' then x' else optimize x'
 where
  optimize' :: (GArrowSkeleton m) a b -> (GArrowSkeleton m) a b

  -- Some optimizations fail due to misparenthesization; we default to
  -- left-associativity and hope for the best
  optimize' (GAS_comp              f (GAS_comp g h)   ) = GAS_comp (GAS_comp f g) h
  optimize' (GAS_comp    (GAS_comp f (GAS_comp g h)) k) = GAS_comp (GAS_comp (GAS_comp f g) h) k
  optimize' (GAS_comp    (GAS_comp             GAS_unassoc  (GAS_second g)) GAS_assoc)   = GAS_second (GAS_second g)
  optimize' (GAS_comp    (GAS_comp (GAS_comp f GAS_unassoc) (GAS_second g)) GAS_assoc)   = GAS_comp f (GAS_second (GAS_second g))

  optimize' (GAS_comp    (GAS_comp f g) h) = case optimize_pair g h of
                                               Nothing   -> GAS_comp (optimize' (GAS_comp f g)) h'
                                               Just ret' -> GAS_comp f' ret'
                                              where
                                                f' = optimize' f
                                                g' = optimize' g
                                                h' = optimize' h
  optimize' (GAS_comp      f g     ) = case optimize_pair f g of
                                         Nothing   -> GAS_comp f' g'
                                         Just ret' -> ret'
                                        where
                                         f' = optimize' f
                                         g' = optimize' g
  optimize' (GAS_first     GAS_id  ) = GAS_id
  optimize' (GAS_second    GAS_id  ) = GAS_id
--  optimize' (GAS_first     (GAS_comp f g)) = GAS_comp (GAS_first  f) (GAS_first g)
--  optimize' (GAS_second    (GAS_comp f g)) = GAS_comp (GAS_second f) (GAS_second g)
  optimize' (GAS_first     f       ) = GAS_first  $ optimize' f
  optimize' (GAS_second    f       ) = GAS_second $ optimize' f
  optimize' (GAS_loopl     GAS_id  ) = GAS_id
  optimize' (GAS_loopr     GAS_id  ) = GAS_id
  optimize' (GAS_loopl     f       ) = GAS_loopl $ optimize' f
  optimize' (GAS_loopr     f       ) = GAS_loopr $ optimize' f
  optimize' x                        = x

  optimize_pair :: (GArrowSkeleton m) a b -> (GArrowSkeleton m) b c -> Maybe ((GArrowSkeleton m) a c)

  optimize_pair f GAS_drop                    = Just $ GAS_drop
  optimize_pair GAS_id f                      = Just $ f
  optimize_pair f GAS_id                      = Just $ f
  optimize_pair GAS_uncancell GAS_cancell     = Just $ GAS_id
  optimize_pair GAS_uncancelr GAS_cancelr     = Just $ GAS_id
  optimize_pair GAS_cancell GAS_uncancell     = Just $ GAS_id
  optimize_pair GAS_cancelr GAS_uncancelr     = Just $ GAS_id
  optimize_pair GAS_uncancelr GAS_cancell     = Just $ GAS_id
  optimize_pair GAS_uncancell GAS_cancelr     = Just $ GAS_id

  -- first priority: eliminate GAS_first                                                
  optimize_pair (GAS_first f) GAS_cancelr     = Just $ GAS_comp   GAS_cancelr f
  optimize_pair (GAS_second f) GAS_cancell    = Just $ GAS_comp   GAS_cancell f
  optimize_pair GAS_uncancelr (GAS_first f)   = Just $ GAS_comp   f GAS_uncancelr
  optimize_pair GAS_uncancell (GAS_second f)  = Just $ GAS_comp   f GAS_uncancell

  -- second priority: push GAS_swap leftward
  optimize_pair (GAS_second f) GAS_swap       = Just $ GAS_comp   GAS_swap (GAS_first  f)
  optimize_pair (GAS_first f) GAS_swap        = Just $ GAS_comp   GAS_swap (GAS_second f)
  optimize_pair GAS_swap GAS_swap             = Just $ GAS_id
  optimize_pair GAS_swap GAS_cancell          = Just $ GAS_cancelr
  optimize_pair GAS_swap GAS_cancelr          = Just $ GAS_cancell

  optimize_pair GAS_assoc   GAS_cancell       = Just $ GAS_first GAS_cancell
  optimize_pair GAS_unassoc GAS_cancelr       = Just $ GAS_second GAS_cancelr
  optimize_pair GAS_assoc   (GAS_second GAS_cancell)  = Just $ GAS_first GAS_cancelr
  optimize_pair GAS_unassoc (GAS_first  GAS_cancell)  = Just $ GAS_cancell


  -- FIXME: valid only for central morphisms
  --optimize_pair (GAS_second f) (GAS_first g) = Just $ GAS_comp (GAS_first g) (GAS_second f)
  optimize_pair (GAS_first g) (GAS_second f) = Just $ GAS_comp  (GAS_second f) (GAS_first g)

  optimize_pair _ _                           = Nothing
-}

repeat :: Eq a => (a -> a) -> a -> a
repeat f x = let x' = f x in
             if x == x'
             then x
             else repeat f x'

--
-- | Recursively turns @(ga_first x >>> first y)@ into @(ga_first (x >>> y))@, likewise for ga_second.
--
beautify :: (GArrowSkeleton m) a b -> (GArrowSkeleton m) a b
beautify = optimize . (repeat beautify')
 where
  beautify' :: (GArrowSkeleton m) a b -> (GArrowSkeleton m) a b
  beautify' (GAS_comp    (GAS_comp f g) h)              = GAS_comp f $ GAS_comp g            h
  beautify' (GAS_comp  f  (GAS_comp (GAS_comp g h) k))  = GAS_comp f $ GAS_comp g $ GAS_comp h k
  beautify' (GAS_comp f (GAS_comp g h)) = case (beautify' f, beautify' g) of
                                            (GAS_first f' , GAS_first  g') -> beautify' $ GAS_comp (GAS_first  (GAS_comp f' g')) h
                                            (GAS_second f', GAS_second g') -> beautify' $ GAS_comp (GAS_second (GAS_comp f' g')) h
                                            (f'           , g'           ) -> GAS_comp f' (beautify' (GAS_comp g h))
  beautify' (GAS_comp f g) = case (beautify' f, beautify' g) of
                              (GAS_first f' , GAS_first  g') -> GAS_first  (GAS_comp f' g')
                              (GAS_second f', GAS_second g') -> GAS_second (GAS_comp f' g')
                              (f'           , g'           ) -> GAS_comp f' g'
  beautify' (GAS_first f)  = GAS_first  $ beautify' f
  beautify' (GAS_second f) = GAS_second $ beautify' f
  beautify' (GAS_loopl f)  = GAS_loopl  $ beautify' f
  beautify' (GAS_loopr f)  = GAS_loopr  $ beautify' f
  beautify' q              = q




gas2gasl :: GArrowSkeleton m x y -> GArrowSkeletonL m x y
gas2gasl (GAS_const k    ) = GASL_Y $ GASY_X $ GASX_const k
gas2gasl (GAS_id         ) = GASL_id
gas2gasl (GAS_comp    f g) = gaslcat (gas2gasl f) (gas2gasl g)
gas2gasl (GAS_first     f) = gasl_firstify  $ gas2gasl f
gas2gasl (GAS_second    f) = gasl_secondify $ gas2gasl f
gas2gasl (GAS_cancell    ) = GASL_Y $ GASY_X $ GASX_cancell
gas2gasl (GAS_cancelr    ) = GASL_Y $ GASY_X $ GASX_cancelr
gas2gasl (GAS_uncancell  ) = GASL_Y $ GASY_X $ GASX_uncancell
gas2gasl (GAS_uncancelr  ) = GASL_Y $ GASY_X $ GASX_uncancelr
gas2gasl (GAS_assoc      ) = GASL_Y $ GASY_X $ GASX_assoc
gas2gasl (GAS_unassoc    ) = GASL_Y $ GASY_X $ GASX_unassoc
gas2gasl (GAS_drop       ) = GASL_Y $ GASY_X $ GASX_drop
gas2gasl (GAS_copy       ) = GASL_Y $ GASY_X $ GASX_copy
gas2gasl (GAS_swap       ) = GASL_Y $ GASY_X $ GASX_swap
gas2gasl (GAS_merge      ) = GASL_Y $ GASY_X $ GASX_merge
gas2gasl (GAS_loopl     f) = GASL_Y $ GASY_X $ GASX_loopl $ gas2gasl f
gas2gasl (GAS_loopr     f) = GASL_Y $ GASY_X $ GASX_loopr $ gas2gasl f
gas2gasl (GAS_misc      m) = GASL_Y $ GASY_X $ GASX_misc m

-- apply "first" to a GASL
gasl_firstify :: GArrowSkeletonL m x y -> GArrowSkeletonL m (x,z) (y,z)
gasl_firstify (GASL_id          ) = GASL_id
gasl_firstify (GASL_Y    gy     ) = GASL_Y $ GASY_first $ gy
gasl_firstify (GASL_comp gxq gqy) = GASL_comp (GASY_first gxq) $ gasl_firstify gqy

-- apply "second" to a GASL
gasl_secondify :: GArrowSkeletonL m x y -> GArrowSkeletonL m (z,x) (z,y)
gasl_secondify (GASL_id          ) = GASL_id
gasl_secondify (GASL_Y    gy     ) = GASL_Y $ GASY_second $ gy
gasl_secondify (GASL_comp gxq gqy) = GASL_comp (GASY_second gxq) $ gasl_secondify gqy

-- concatenates two GASL's
gaslcat :: GArrowSkeletonL m x y -> GArrowSkeletonL m y z -> GArrowSkeletonL m x z
gaslcat (GASL_id          ) g' = g'
gaslcat (GASL_Y    gy     ) g' = GASL_comp gy g'
gaslcat (GASL_comp gxq gqy) g' = GASL_comp gxq (gaslcat gqy g')

data GArrowSkeletonL m :: * -> * -> *
 where
  GASL_id        ::                                                   GArrowSkeletonL m x x
  GASL_Y         :: GArrowSkeletonY m x y                          -> GArrowSkeletonL m x y
  GASL_comp      :: GArrowSkeletonY m x y -> GArrowSkeletonL m y z -> GArrowSkeletonL m x z

data GArrowSkeletonY m :: * -> * -> *
 where
  GASY_X         :: GArrowSkeletonX m x y                        -> GArrowSkeletonY m x y
  GASY_first     :: GArrowSkeletonY m x y                        -> GArrowSkeletonY m (x,z)  (y,z)
  GASY_second    :: GArrowSkeletonY m x y                        -> GArrowSkeletonY m (z,x)  (z,y)

data GArrowSkeletonX m :: * -> * -> *
 where
  GASX_const     ::                                          Int -> GArrowSkeletonX m () Int
  GASX_cancell   ::                                                 GArrowSkeletonX m ((),x) x
  GASX_cancelr   ::                                                 GArrowSkeletonX m (x,()) x
  GASX_uncancell ::                                                 GArrowSkeletonX m x ((),x)
  GASX_uncancelr ::                                                 GArrowSkeletonX m x (x,())
  GASX_assoc     ::                                                 GArrowSkeletonX m ((x,y),z) (x,(y,z))
  GASX_unassoc   ::                                                 GArrowSkeletonX m (x,(y,z)) ((x,y),z)
  GASX_drop      ::                                                 GArrowSkeletonX m x         ()
  GASX_copy      ::                                                 GArrowSkeletonX m x         (x,x)
  GASX_swap      ::                                                 GArrowSkeletonX m (x,y)     (y,x)
  GASX_merge     ::                                                 GArrowSkeletonX m (x,y)     z
  GASX_misc      ::                                        m x y -> GArrowSkeletonX m x y
  GASX_loopl     ::                GArrowSkeletonL m (z,x) (z,y) -> GArrowSkeletonX m x y
  GASX_loopr     ::                GArrowSkeletonL m (x,z) (y,z) -> GArrowSkeletonX m x y

-- TO DO: gather "maximal chunks" of ga_first/ga_second
gasl2gas :: GArrowSkeletonL m x y -> GArrowSkeleton m x y
gasl2gas GASL_id           = GAS_id
gasl2gas (GASL_Y    gy   ) = gasy2gas gy
gasl2gas (GASL_comp gy gl) = GAS_comp (gasy2gas gy) (gasl2gas gl)

gasy2gas :: GArrowSkeletonY m x y -> GArrowSkeleton m x y
gasy2gas (GASY_X      gx)  = gasx2gas gx
gasy2gas (GASY_first  gy)  = GAS_first (gasy2gas gy)
gasy2gas (GASY_second gy)  = GAS_second (gasy2gas gy)

gasx2gas :: GArrowSkeletonX m x y -> GArrowSkeleton m x y
gasx2gas (GASX_const k)    = GAS_const k
gasx2gas (GASX_cancell)    = GAS_cancell
gasx2gas (GASX_cancelr)    = GAS_cancelr
gasx2gas (GASX_uncancell)  = GAS_uncancell
gasx2gas (GASX_uncancelr)  = GAS_uncancelr
gasx2gas (GASX_assoc)      = GAS_assoc
gasx2gas (GASX_unassoc)    = GAS_unassoc
gasx2gas (GASX_drop)       = GAS_drop
gasx2gas (GASX_copy)       = GAS_copy
gasx2gas (GASX_swap)       = GAS_swap
gasx2gas (GASX_merge)      = GAS_merge
gasx2gas (GASX_misc m)     = GAS_misc m
gasx2gas (GASX_loopl gl)   = GAS_loopl $ gasl2gas gl
gasx2gas (GASX_loopr gl)   = GAS_loopr $ gasl2gas gl



optimizel :: GArrowSkeletonL m x y -> GArrowSkeletonL m x y
optimizel (GASL_id        )                                                                                = GASL_id
optimizel (GASL_Y    gy   )                                                                                = GASL_Y $ optimizey gy
optimizel (GASL_comp gy (GASL_comp gy' gl)) | pushright gy, not (pushright gy'), Just x <- pushpair gy gy' = optimizel $ gaslcat x gl
optimizel (GASL_comp gy (GASL_Y gy'))       | pushright gy, not (pushright gy'), Just x <- pushpair gy gy' = GASL_comp (optimizey gy) (GASL_Y gy')
optimizel (GASL_comp gy (GASL_comp gy' gl)) | Just x <- optpair gy gy'                                     = optimizel $ gaslcat x gl
optimizel (GASL_comp gy (GASL_Y gy'))       | Just x <- optpair gy gy'                                     = GASL_comp (optimizey gy) (GASL_Y gy')
optimizel (GASL_comp gy gl)                                                                                = GASL_comp (optimizey gy) (optimizel gl)

--optimize' (GAS_loopl     GAS_id  ) = GAS_id
--optimize' (GAS_loopr     GAS_id  ) = GAS_id
--optimize_pair f GAS_drop                    = Just $ GAS_drop
{-
  optimize_pair (GAS_first f) GAS_cancelr     = Just $ GAS_comp   GAS_cancelr f
  optimize_pair (GAS_second f) GAS_cancell    = Just $ GAS_comp   GAS_cancell f
  optimize_pair GAS_uncancelr (GAS_first f)   = Just $ GAS_comp   f GAS_uncancelr
  optimize_pair GAS_uncancell (GAS_second f)  = Just $ GAS_comp   f GAS_uncancell
  optimize_pair (GAS_second f) GAS_swap       = Just $ GAS_comp   GAS_swap (GAS_first  f)
  optimize_pair (GAS_first f) GAS_swap        = Just $ GAS_comp   GAS_swap (GAS_second f)
  optimize_pair GAS_swap GAS_swap             = Just $ GAS_id
  optimize_pair GAS_swap GAS_cancell          = Just $ GAS_cancelr
  optimize_pair GAS_swap GAS_cancelr          = Just $ GAS_cancell
  optimize_pair GAS_assoc   GAS_cancell       = Just $ GAS_first GAS_cancell
  optimize_pair GAS_unassoc GAS_cancelr       = Just $ GAS_second GAS_cancelr
  optimize_pair GAS_assoc   (GAS_second GAS_cancell)  = Just $ GAS_first GAS_cancelr
  optimize_pair GAS_unassoc (GAS_first  GAS_cancell)  = Just $ GAS_cancell
-}

optpair :: GArrowSkeletonY m x y -> GArrowSkeletonY m y z -> Maybe (GArrowSkeletonL m x z)
optpair (GASY_first  gy1) (GASY_first  gy2)           = liftM gasl_firstify  $ optpair gy1 gy2
optpair (GASY_second gy1) (GASY_second gy2)           = liftM gasl_secondify $ optpair gy1 gy2
optpair (GASY_X GASX_uncancell) (GASY_X GASX_cancell) = Just $ GASL_id
optpair (GASY_X GASX_uncancelr) (GASY_X GASX_cancelr) = Just $ GASL_id
optpair (GASY_X GASX_cancell) (GASY_X GASX_uncancell) = Just $ GASL_id
optpair (GASY_X GASX_cancelr) (GASY_X GASX_uncancelr) = Just $ GASL_id
optpair (GASY_X GASX_uncancelr) (GASY_X GASX_cancell) = Just $ GASL_id
optpair (GASY_X GASX_uncancell) (GASY_X GASX_cancelr) = Just $ GASL_id
optpair _ _ = Nothing

pushpair :: GArrowSkeletonY m x y -> GArrowSkeletonY m y z -> Maybe (GArrowSkeletonL m x z)
pushpair (GASY_first  gy1) (GASY_first  gy2)                 = liftM gasl_firstify  $ pushpair gy1 gy2
pushpair (GASY_second gy1) (GASY_second gy2)                 = liftM gasl_secondify $ pushpair gy1 gy2
pushpair (GASY_first  gy1) (GASY_second gy2)                 = Just $ GASL_comp (GASY_second gy2) (GASL_Y $ GASY_first  gy1)
pushpair (GASY_second gy1) (GASY_first  gy2)                 = Just $ GASL_comp (GASY_first  gy2) (GASL_Y $ GASY_second gy1)
pushpair (GASY_first  gy1) (GASY_X GASX_unassoc) = Just $ GASL_comp(GASY_X GASX_unassoc) (GASL_Y $ GASY_first  (GASY_first  gy1))
pushpair (GASY_second gy1) (GASY_X GASX_assoc  ) = Just $ GASL_comp(GASY_X GASX_assoc  ) (GASL_Y $ GASY_second (GASY_second gy1))
pushpair (GASY_second (GASY_X GASX_uncancelr)) (GASY_X GASX_unassoc  ) = Just $ GASL_Y $ GASY_X GASX_uncancelr
pushpair (GASY_first  (GASY_X GASX_uncancell)) (GASY_X GASX_assoc    ) = Just $ GASL_Y $ GASY_X GASX_uncancell
pushpair (GASY_X GASX_uncancelr) (GASY_first gy)  = Just $ GASL_comp gy (GASL_Y $ GASY_X $ GASX_uncancelr)
pushpair (GASY_X GASX_uncancell) (GASY_second gy) = Just $ GASL_comp gy (GASL_Y $ GASY_X $ GASX_uncancell)
pushpair (GASY_first  (GASY_second gy)) (GASY_X GASX_assoc    ) = Just $ GASL_comp (GASY_X GASX_assoc  ) $ GASL_Y (GASY_second (GASY_first  gy))
pushpair (GASY_second (GASY_first  gy)) (GASY_X GASX_unassoc  ) = Just $ GASL_comp (GASY_X GASX_unassoc) $ GASL_Y (GASY_first  (GASY_second gy))
pushpair (GASY_second (GASY_second gy)) (GASY_X GASX_unassoc  ) = Just $ GASL_comp (GASY_X GASX_unassoc) $ GASL_Y (GASY_second gy)
pushpair (GASY_first  (GASY_first  gy)) (GASY_X GASX_assoc    ) = Just $ GASL_comp (GASY_X GASX_assoc)   $ GASL_Y (GASY_first gy)
pushpair (GASY_X GASX_uncancell) (GASY_X GASX_unassoc ) = Just $ GASL_Y $ GASY_first  $ GASY_X GASX_uncancell
pushpair (GASY_X GASX_uncancelr) (GASY_X GASX_assoc   ) = Just $ GASL_Y $ GASY_second $ GASY_X GASX_uncancelr
pushpair (GASY_first  (GASY_X GASX_uncancelr)) (GASY_X GASX_assoc    ) = Just $ GASL_Y $ GASY_second $ GASY_X GASX_uncancell
pushpair (GASY_second (GASY_X GASX_uncancell)) (GASY_X GASX_unassoc  ) = Just $ GASL_Y $ GASY_first  $ GASY_X GASX_uncancelr
pushpair (GASY_first  gy) (GASY_X GASX_swap    ) = Just $ GASL_comp (GASY_X GASX_swap) $ GASL_Y (GASY_second  gy)
pushpair (GASY_second gy) (GASY_X GASX_swap    ) = Just $ GASL_comp (GASY_X GASX_swap) $ GASL_Y (GASY_first   gy)
pushpair (GASY_X GASX_uncancell) (GASY_X GASX_swap    ) = Just $ GASL_Y $ GASY_X $ GASX_uncancelr
pushpair (GASY_X GASX_uncancelr) (GASY_X GASX_swap    ) = Just $ GASL_Y $ GASY_X $ GASX_uncancell
pushpair _ _                                 = Nothing

-- pushright can only return True for central morphisms
pushright :: GArrowSkeletonY m x y -> Bool
pushright (GASY_first  gy)              = pushright gy
pushright (GASY_second gy)              = pushright gy
pushright (GASY_X      GASX_uncancell)  = True
pushright (GASY_X      GASX_uncancelr)  = True
pushright (GASY_X      _             )  = False

optimizey :: GArrowSkeletonY m x y -> GArrowSkeletonY m x y
optimizey (GASY_X      gx)  = GASY_X $ optimizex gx
optimizey (GASY_first  gy)  = GASY_first (optimizey gy)
optimizey (GASY_second gy)  = GASY_second (optimizey gy)

optimizex :: GArrowSkeletonX m x y -> GArrowSkeletonX m x y
optimizex (GASX_const k)    = GASX_const k
optimizex (GASX_cancell)    = GASX_cancell
optimizex (GASX_cancelr)    = GASX_cancelr
optimizex (GASX_uncancell)  = GASX_uncancell
optimizex (GASX_uncancelr)  = GASX_uncancelr
optimizex (GASX_assoc)      = GASX_assoc
optimizex (GASX_unassoc)    = GASX_unassoc
optimizex (GASX_drop)       = GASX_drop
optimizex (GASX_copy)       = GASX_copy
optimizex (GASX_swap)       = GASX_swap
optimizex (GASX_merge)      = GASX_merge
optimizex (GASX_misc m)     = GASX_misc m
optimizex (GASX_loopl gl)   = GASX_loopl $ optimizel gl
optimizex (GASX_loopr gl)   = GASX_loopr $ optimizel gl
