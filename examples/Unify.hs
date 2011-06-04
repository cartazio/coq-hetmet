-- | A very simple finite-sized-term unification engine; used by GArrowTikZ
module Unify(UVar, Unifier, Unifiable(..), mergeU, emptyUnifier, getU, uvarSupply, unify, resolve)
-- 
-- | Terminology: a value of type @t@ (for which an instance
-- @Unifiable t@ exists) is "fully resolved" with respect to some
-- value of type @Unifier t@ if no @UVar@ which occurs in the
-- @t@-value is a key in the unifier map.
--
where
import Prelude hiding (lookup)
import Data.Map hiding (map)
import Data.Tree
import Data.List (nub)
import Control.Monad.Error

-- | a unification variable
newtype UVar = UVar Int
 deriving (Ord, Eq)

instance Show UVar where
 show (UVar v) = "u" ++ show v

-- | A unifier is a map from unification /variables/ to unification
-- /values/ of type @t@.  Invariant: values of the map are always
-- fully resolved with respect to the map.
data Unifier t = Unifier (Map UVar t)
               | UnifierError String

-- | Resolves a unification variable according to a Unifier.
getU :: Unifier t -> UVar -> Maybe t
getU (Unifier      u) v = lookup v u
getU (UnifierError e) v = error e

-- | An infinite supply of distinct unification variables.
uvarSupply :: [UVar]
uvarSupply = uvarSupply' 0
              where
               uvarSupply' n = (UVar n):(uvarSupply' $ n+1)

-- | The empty unifier.
emptyUnifier :: Unifier t
emptyUnifier =  Unifier empty

-- | Types for which we know how to do unification.
class Show t => Unifiable t where

  -- | Turns a @UVar@ into a @t@
  inject      :: UVar -> t

  -- | Discern if a @t@ is a @UVar@.  Invariant: @(project (inject x) == x)@
  project     :: t -> Maybe UVar

  -- | Instances must implement this; it is called by @(unify x y)@
  --   only when both @(project x)@ and @(project y)@ are @Nothing@
  unify'      :: t -> t -> Unifier t

  -- | Returns a list of all @UVars@ occurring in @t@
  occurrences :: t -> [UVar]

  -- | @(replace vrep trep t)@ returns a copy of @t@ in which all occurrences of @vrep@ have been replaced by @trep@
  replace     :: UVar -> t -> t -> t

-- | Returns a copy of the @t@ argument in which all @UVar@
-- occurrences have been replaced by fully-resolved @t@ values.
resolve :: Unifiable t => Unifier t -> t -> t
resolve (UnifierError e) _ = error e
resolve (Unifier m) t      = resolve' (toList m) t
 where
  resolve' []            t                         = t
  resolve' ((uv,v):rest) t | Just uvt <- project t = if uvt == uv
                                                     then v        -- we got this out of the unifier, so it must be fully resolved
                                                     else resolve' rest t
                           | otherwise             = resolve' rest (replace uv v t)

-- | Given two unifiables, find their most general unifier.
unify :: Unifiable t => t -> t -> Unifier t
unify v1 v2 | (Just v1') <- project v1, (Just v2') <- project v2, v1'==v2'  = emptyUnifier
unify v1 v2 | (Just v1') <- project v1                                      = if  elem v1' (occurrences v2)
                                                                              then UnifierError "occurs check failed in Unify.unify"
                                                                              else Unifier $ insert v1' v2 empty
unify v1 v2 | (Just v2') <- project v2                                      = unify v2 v1
unify v1 v2 |  _         <- project v1,  _         <- project v2            = unify' v1 v2

-- | Merge two unifiers into a single unifier.
mergeU :: Unifiable t => Unifier t -> Unifier t -> Unifier t
mergeU ue@(UnifierError _) _  = ue
mergeU    (Unifier      u) u' = foldr (\(k,v) -> \uacc -> mergeU' uacc k (resolve uacc v)) u' (toList u)
 where
  mergeU' ue@(UnifierError _) _ _                                              = ue
  mergeU'  u@(Unifier m) v1 v2 | member v1 m                                   = mergeU u $ unify (m ! v1) v2
                               | Just v2' <- project (resolve u v2), v2' == v1 = u
                               | elem v1 (occurrences v2)                      = UnifierError "occurs check failed in Unify.mergeU"
                               | otherwise                                     = Unifier $ insert v1 v2 m
                                                           
-- | Enumerates the unification variables, sorted by occurs-check.
sortU :: (Unifiable t, Eq t) => Unifier t -> [UVar]
sortU u@(Unifier um)      = reverse $ nub $ concatMap (\k -> occurrences (um!k)) (keys um)
sortU   (UnifierError ue) = error ue
