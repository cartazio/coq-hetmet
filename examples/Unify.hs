-- | A very simple unification engine; used by GArrowTikZ
module Unify(UVar, Unifier, Unifiable(..), mergeU, emptyUnifier, getU, uvarSupply, unify, resolve, occurs)
where
import Prelude hiding (lookup)
import Data.Map hiding (map)
import Data.Tree
import Data.List (nub)
import Control.Monad.Error

-- TO DO: propagate occurs-check errors through the Unifier instead of using Prelude.error

-- | a unification variable
newtype UVar = UVar Int
 deriving (Ord, Eq)

instance Show UVar where
 show (UVar v) = "u" ++ show v

-- | A unifier is a map from unification /variables/ to unification /values/ of type @t@.
data Unifier t = Unifier (Map UVar t)

-- | Resolves a unification variable according to a Unifier (not recursively).
getU :: Unifier t -> UVar -> Maybe t
getU (Unifier u) v = lookup v u

-- | An infinite supply of distinct unification variables.
uvarSupply :: [UVar]
uvarSupply = uvarSupply' 0
              where
               uvarSupply' n = (UVar n):(uvarSupply' $ n+1)

-- | The empty unifier.
emptyUnifier :: Unifier t
emptyUnifier =  Unifier empty

-- | Types for which we know how to do unification.
class Unifiable t where

  -- | Turns a @UVar@ into a @t@
  inject      :: UVar -> t

  -- | Discern if a @t@ is a @UVar@.  Invariant: @(project (inject x) == x)@
  project     :: t -> Maybe UVar

  -- | Instances must implement this; it is called by @(unify x y)@
  --   only when both @(project x)@ and @(project y)@ are @Nothing@
  unify'  :: t -> t -> Unifier t

  -- | Returns a list of all @UVars@ occurring in @t@; duplicates are okay and resolution should not be performed.
  occurrences :: t -> [UVar]

-- | Returns a list of all UVars occurring anywhere in t and any UVars which
--   occur in values unified therewith.
resolve :: Unifiable t => Unifier t -> UVar -> [UVar]
resolve (Unifier u) v | member v u = v:(concatMap (resolve (Unifier u)) $ occurrences $ u ! v)
                      | otherwise  = [v]

-- | The occurs check.
occurs :: Unifiable t => Unifier t -> UVar -> t -> Bool
occurs u v x = elem v $ concatMap (resolve u) (occurrences x)

-- | Given two unifiables, find their most general unifier.  Do not override this.
unify :: Unifiable t => t -> t -> Unifier t
unify v1 v2 | (Just v1') <- project v1, (Just v2') <- project v2, v1'==v2'                   = emptyUnifier
unify v1 v2 | (Just v1') <- project v1 = if  occurs emptyUnifier v1' v2 
                                         then error "occurs check failed"
                                         else Unifier $ insert v1' v2 empty
unify v1 v2 | (Just v2') <- project v2 = unify v2 v1
unify v1 v2 |  _         <- project v1,  _         <- project v2                             = unify' v1 v2

-- | Merge two unifiers into a single unifier.
mergeU :: Unifiable t => Unifier t -> Unifier t -> Unifier t
mergeU (Unifier u) u' = foldr (\(k,v) -> \uacc -> mergeU' uacc k v) u' (toList u)
 where
  mergeU' u@(Unifier m) v1 v2 | member v1 m    = mergeU u $ unify (m ! v1) v2
                              | occurs u v1 v2 = error "occurs check failed"
                              | otherwise      = Unifier $ insert v1 v2 m
                                                           
-- | Enumerates the unification variables, sorted by occurs-check.
sortU :: (Unifiable t, Eq t) => Unifier t -> [UVar]
sortU u@(Unifier um) = reverse $ nub $ concatMap (resolve u) (keys um)


