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
module GArrowSkeleton (GArrowSkeleton(..), optimize)
where
import Prelude hiding ( id, (.), lookup )
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

instance GArrowSTKC (GArrowSkeleton m)

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
optimize x = let x' = optimize' x in if x == x' then x' else optimize x'
 where
  optimize' :: (GArrowSkeleton m) a b -> (GArrowSkeleton m) a b

  -- Some optimizations fail due to misparenthesization; we default to
  -- left-associativity and hope for the best
  optimize' (GAS_comp      f (GAS_comp g h)) = GAS_comp (GAS_comp f g) h
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
  optimize' (GAS_first     f       ) = GAS_first  $ optimize' f
  optimize' (GAS_second    f       ) = GAS_second $ optimize' f
  optimize' (GAS_loopl GAS_id)  = GAS_id
  optimize' (GAS_loopr GAS_id)  = GAS_id
  optimize' (GAS_loopl f      ) = GAS_loopl $ optimize' f
  optimize' (GAS_loopr f      ) = GAS_loopr $ optimize' f
  optimize' x                   = x

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

  optimize_pair (GAS_first f) (GAS_first g)   = Just $ GAS_first (GAS_comp f g)
  optimize_pair (GAS_second f) (GAS_second g) = Just $ GAS_second (GAS_comp f g)

  optimize_pair GAS_assoc   GAS_cancell       = Just $ GAS_first GAS_cancell
  optimize_pair GAS_unassoc GAS_cancelr       = Just $ GAS_second GAS_cancelr
  optimize_pair GAS_assoc   (GAS_second GAS_cancell)  = Just $ GAS_first GAS_cancelr
  optimize_pair GAS_unassoc (GAS_first  GAS_cancell)  = Just $ GAS_cancell


  -- FIXME: valid only for central morphisms
  --optimize_pair (GAS_second f) (GAS_first g) = Just $ GAS_comp (GAS_first g) (GAS_second f)
  optimize_pair (GAS_first g) (GAS_second f) = Just $ GAS_comp  (GAS_second f) (GAS_first g)

  optimize_pair _ _                           = Nothing


