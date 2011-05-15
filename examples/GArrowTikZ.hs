{-# LANGUAGE RankNTypes, MultiParamTypeClasses, GADTs, FlexibleContexts, FlexibleInstances, TypeOperators #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  GArrowTikZ
-- Copyright   :  none
-- License     :  public domain
--
-- Maintainer  :  Adam Megacz <megacz@acm.org>
-- Stability   :  experimental
--
-- | Renders a @GArrowSkeleton@ using TikZ; the result is LaTeX code
--

module GArrowTikZ (tikz, tikz')
where
import Prelude hiding ( id, (.), lookup )
import Control.Category
import GHC.HetMet.GArrow
import Data.List hiding (lookup, insert)
import Data.Map hiding (map, (!))
import Unify
import GArrowSkeleton
import GHC.HetMet.Private

data UPort =
   UPortVar  UVar
 | UPortPair UPort UPort

instance Unifiable UPort where
  unify' (UPortPair vl1a vl1b) (UPortPair vl2a vl2b) = mergeU (unify vl1a vl2a) (unify vl1b vl2b)
  unify' _ _                                         = error "impossible"
  inject                                             = UPortVar
  project (UPortVar v)                               = Just v
  project _                                          = Nothing
  occurrences (UPortVar v)                           = [v]
  occurrences (UPortPair x y)                        = occurrences x ++ occurrences y

-- | Resolves a unification variable; the answer to this query will change if subsequent unifications are performed
getU' :: Unifier UPort -> UPort -> UPort
getU' u (UPortPair x y)  = UPortPair (getU' u x) (getU' u y)
getU' u x@(UPortVar v)   = case Unify.getU u v  of
                                     Nothing -> x
                                     Just x' -> getU' u x'




--
-- | Render a fully-polymorphic GArrow term as a boxes-and-wires diagram using TikZ
--

type Constraints = [(UPort, Int, UPort)]

-- the unification monad
data UyM t a = UyM (([UVar],Unifier UPort,Constraints) -> ([UVar],Unifier UPort,Constraints,a))
instance Monad (UyM t)
 where
  return x      = UyM $ \(i,u,k) -> (i,u,k,x)
  (UyM f) >>= g = UyM $ \(i,u,k) -> let (i',u',k',x) = f (i,u,k) in let UyM g' = g x in g' (i',u',k')


getU        = UyM $ \(i,u,k) -> (i,u,k,u)
getM    v   = UyM $ \(i,u,k) -> (i,u,k,getU' u v)
occursU v x = UyM $ \(i,u,k) -> (i,u,k,occurs u v x)
unifyM :: Eq t => UPort -> UPort -> UyM t ()
unifyM v1 v2 = UyM $ \(i,u,k) -> (i,mergeU u (unify v1 v2),k,())
freshU :: UyM t UVar
freshU = UyM $ \(i:is,u,k) -> (is,u,k,i)
constrain :: UPort -> Int -> UPort -> UyM t ()
constrain v1 d v2 = UyM $ \(i,u,k) -> (i,u,((v1,d,v2):k),())
getK :: UyM t [(UPort, Int, UPort)]
getK = UyM $ \(i,u,k) -> (i,u,k,k)
runU :: UyM t a -> ([UVar],Unifier UPort,Constraints,a)
runU (UyM f) = (f (uvarSupply,emptyUnifier,[]))



name :: GArrowSkeleton m a b -> String
name GAS_id              = "id"
name (GAS_const i)       = "const " ++ show i
name (GAS_comp      _ _) = "comp"
name (GAS_first     _  ) = "first"
name (GAS_second    _  ) = "second"
name GAS_cancell         = "cancell"
name GAS_cancelr         = "cancelr"
name GAS_uncancell       = "uncancell"
name GAS_uncancelr       = "uncancelr"
name GAS_drop            = "drop"
name GAS_copy            = "copy"
name GAS_swap            = "swap"
name (GAS_loopl     _ )  = "loopl"
name (GAS_loopr     _ )  = "loopr"
name GAS_assoc           = "assoc"
name GAS_unassoc         = "unassoc"
name GAS_merge           = "merge"
name (GAS_misc _)        = "misc"

fresh :: Int -> UyM () [Ports]
fresh 0 = return []
fresh n = do { xs <- fresh  (n-1)
             ; x  <- freshU
             ; case xs of
                 []       -> return [UPortVar x]
                 (x':xs') -> do { constrain (UPortVar x) 1 x'
                                ; return $ (UPortVar x):x':xs'
                                }
             }

data Diagram p = DiagramComp      (Diagram p) (Diagram p)
               | DiagramPrim      String p p p p (String -> Int -> Int -> Int -> p -> p -> Int -> String)
               | DiagramBypassTop p (Diagram p)
               | DiagramBypassBot (Diagram p) p
               -- | DiagramLoopTop   Diagram
               -- | DiagramLoopBot   Diagram

type Ports = UPort

getOut :: Diagram Ports -> Ports
getOut (DiagramComp f g)                     = getOut g
getOut (DiagramPrim s ptop pin pout pbot _)  = pout
getOut (DiagramBypassTop p f)                = UPortPair p (getOut f)
getOut (DiagramBypassBot f p)                = UPortPair (getOut f) p

getIn :: Diagram Ports -> Ports
getIn (DiagramComp f g)                      = getIn f
getIn (DiagramPrim s ptop pin pout pbot _)   = pin
getIn (DiagramBypassTop p f)                 = UPortPair p (getIn f)
getIn (DiagramBypassBot f p)                 = UPortPair (getIn f) p

-- constrain that Ports is at least Int units above the topmost portion of Diagram
constrainTop :: Ports -> Int -> Diagram Ports -> UyM () ()
constrainTop v i (DiagramComp d1 d2)                  = do { constrainTop v i d1 ; constrainTop v i d2 ; return () }
constrainTop v i (DiagramBypassTop p d)               = constrain v 2 p
constrainTop v i (DiagramBypassBot d p)               = constrainTop v (i+1) d
constrainTop v i (DiagramPrim s ptop pin pout pbot _) = constrain v i ptop

-- constrain that Ports is at least Int units below the bottommost portion of Diagram
constrainBot :: Diagram Ports -> Int -> Ports -> UyM () ()
constrainBot (DiagramComp d1 d2)                  i v = do { constrainBot d1 i v ; constrainBot d2 i v ; return () }
constrainBot (DiagramBypassTop p d)               i v = constrainBot d (i+1) v
constrainBot (DiagramBypassBot d p)               i v = constrain p 2 v
constrainBot (DiagramPrim s ptop pin pout pbot _) i v = constrain pbot i v

ga2diag :: GArrowSkeleton m a b -> UyM () (Diagram Ports)
ga2diag (GAS_id           ) = do { [top,x,bot] <- fresh 3 ; return $ DiagramPrim "id" top x x bot defren }
ga2diag (GAS_comp      f g) = do { f' <- ga2diag f
                                  ; g' <- ga2diag g
                                  ; unifyM (getOut f') (getIn g')
                                  ; return $ DiagramComp f' g' }
ga2diag (GAS_first  f) = do { [x] <- fresh 1; f' <- ga2diag f ; constrainBot f' 1 x  ; return $ DiagramBypassBot f' x  }
ga2diag (GAS_second f) = do { [x] <- fresh 1; f' <- ga2diag f ; constrainTop x  1 f' ; return $ DiagramBypassTop x f'  }
ga2diag GAS_cancell    = do { [top,x,y  ,bot] <- fresh 4  ; return $ DiagramPrim   "cancell" top (UPortPair x y) y bot defren }
ga2diag GAS_cancelr    = do { [top,x,y  ,bot] <- fresh 4  ; return $ DiagramPrim   "cancelr" top (UPortPair x y) x bot defren }
ga2diag GAS_uncancell  = do { [top,x,y  ,bot] <- fresh 4  ; return $ DiagramPrim "uncancell" top y (UPortPair x y) bot defren }
ga2diag GAS_uncancelr  = do { [top,x,y  ,bot] <- fresh 4  ; return $ DiagramPrim "uncancelr" top x (UPortPair x y) bot defren }
ga2diag GAS_drop       = do { [top,x    ,bot] <- fresh 3  ; return $ DiagramPrim      "drop" top x x bot defren }
ga2diag (GAS_const i)  = do { [top,x    ,bot] <- fresh 3  ; return $ DiagramPrim  ("const " ++ show i) top x x bot defren }
ga2diag GAS_copy       = do { [top,x,y,z,bot] <- fresh 5
                             ; return $ DiagramPrim      "copy" top y (UPortPair x z) bot defren }
ga2diag GAS_merge      = do { [top,x,y,z,bot] <- fresh 5
                             ; return $ DiagramPrim      "merge" top (UPortPair x z) y bot defren }
ga2diag GAS_swap       = do { [top,x,y  ,bot] <- fresh 4
                             ; return $ DiagramPrim      "swap" top (UPortPair x y) (UPortPair x y) bot defren }
ga2diag GAS_assoc      = do { [top,x,y,z,bot] <- fresh 5
                             ; return $ DiagramPrim  "assoc" top (UPortPair (UPortPair x y) z) (UPortPair x (UPortPair y z)) bot defren }
ga2diag GAS_unassoc    = do { [top,x,y,z,bot] <- fresh 5
                             ; return $ DiagramPrim "unassoc" top (UPortPair x (UPortPair y z)) (UPortPair (UPortPair x y) z) bot defren }
ga2diag (GAS_loopl f) = error "not implemented"
ga2diag (GAS_loopr f) = error "not implemented"
ga2diag (GAS_misc f ) = error "not implemented"

defren :: String -> Int -> Int -> Int -> Ports -> Ports -> Int -> String
defren s x w top p1 p2 bot
      = drawBox x top (x+w) bot "black" s
--        ++ wires (x-1) p1  x    "green"
--        ++ wires  (x+w) p2 (x+w+1) "red"

xscale = 1
yscale = 1

textc x y text color = 
    "\\node[anchor=center,color="++color++"] at ("++show (x*xscale)++"cm,"++show (y*yscale)++"cm) "++
    "{{\\tt{"++text++"}}};\n"

drawBox x1 y1 x2 y2 color text =
    "\\node[anchor=north west] at ("++show (x1*xscale)++"cm,"++show (y1*yscale)++"cm) "++
    "{{\\tt{"++text++"}}};\n"
    ++
    "\\path[draw,color="++color++"]"++
       " ("++show (x1*xscale)++","++show (y1*yscale)++") rectangle ("++
           show (x2*xscale)++","++show (y2*yscale)++");\n"

drawLine x1 y1 x2 y2 color style =
  "\\path[draw,color="++color++","++style++"] "++
  "("++show (x1*xscale)++","++show (y1*yscale)++") -- " ++
  "("++show (x2*xscale)++","++show (y2*yscale)++");\n"

width :: Diagram Ports -> Int
width (DiagramComp d1 d2)         = (width d1) + 1 + (width d2)
width (DiagramPrim s _ p1 p2 _ _) = 2
width (DiagramBypassTop p d)      = (width d) + 2
width (DiagramBypassBot d p)      = (width d) + 2

(!) :: Map UVar Int -> UVar -> Int
m ! x = case lookup x m of
          Nothing -> 0
          Just y -> y

tikZ :: Map UVar Int ->
        Diagram Ports ->
        Int ->                -- horizontal position
        String
tikZ m = tikZ'
 where
  tikZ'  d@(DiagramComp d1 d2)    x = tikZ' d1 x
                                      ++ wires (x+width d1) (getOut d1) (x+width d1+1) "black"
                                      ++ tikZ' d2 (x + width d1 + 1)
  tikZ' d'@(DiagramBypassTop p d) x = let top = getTop d' in
                                      let bot = getBot d' in
                                      drawBox  x top (x+width d') bot "gray!50" "second"
                                      ++ wires x (getIn d) (x+1) "black"
                                      ++ tikZ' d (x+1)
                                      ++ wires (x+1+width d) (getOut d) (x+1+width d+1) "black"
                                      ++ wires x p (x+1+width d+1) "black"
  tikZ' d'@(DiagramBypassBot d p) x = let top = getTop d' in
                                      let bot = getBot d' in
                                      drawBox  x top (x+width d') bot "gray!50" "first"
                                      ++ wires x (getIn d) (x+1) "black"
                                      ++ tikZ' d (x+1)
                                      ++ wires (x+1+width d) (getOut d) (x+1+width d+1) "black"
                                      ++ wires x p (x+1+width d+1) "black"
  tikZ'  d@(DiagramPrim s (UPortVar top) p1 p2 (UPortVar bot) r)  x = r s x (width d) (m ! top) p1 p2 (m ! bot)
  tikZ'  _ _ = error "FIXME"

  wires :: Int -> Ports -> Int -> String -> String
  wires x1 (UPortVar v)    x2 color = drawLine x1 (m ! v) x2 (m ! v) color "->"
                                       --  ++ textc ((x1+x2) `div` 2) (m!v) (show v) "purple"
  wires x1 (UPortPair x y) x2 color = wires x1 x x2 color ++ wires x1 y x2 color

  getTop :: Diagram Ports -> Int
  getTop (DiagramComp d1 d2)                = min (getTop d1) (getTop d2)
  getTop (DiagramBypassTop p d)             = (m ! getleft p) - 1
  getTop (DiagramBypassBot d p)             = getTop d - 1
  getTop (DiagramPrim s (UPortVar ptop) _ _ _ _)  = m ! ptop
  getTop _ = error "getTop failed"

  getBot :: Diagram Ports -> Int
  getBot (DiagramComp d1 d2)                = max (getBot d1) (getBot d2)
  getBot (DiagramBypassTop p d)             = getBot d + 1
  getBot (DiagramBypassBot d p)             = (m ! getright p) + 1
  getBot (DiagramPrim s _ _ _ (UPortVar pbot) _)  = m ! pbot
  getBot _ = error "getTop failed"

resolve' (DiagramComp d1 d2)    = do { d1' <- resolve' d1 ; d2' <- resolve' d2 ; return $ DiagramComp d1' d2'    }
resolve' (DiagramBypassTop p d) = do { p'  <- getM p     ; d'  <- resolve' d  ; return $ DiagramBypassTop p' d' }
resolve' (DiagramBypassBot d p) = do { p'  <- getM p     ; d'  <- resolve' d  ; return $ DiagramBypassBot d' p' }
resolve' (DiagramPrim s ptop pin pout pbot r) 
    = do { ptop' <- getM ptop
         ; pbot' <- getM pbot
         ; pin'  <- getM pin
         ; pout' <- getM pout
         ; return $ DiagramPrim s ptop' pin' pout' pbot' r }

getleft (UPortVar   v)  = v
getleft (UPortPair a b) = getleft a

getright (UPortVar   v)  = v
getright (UPortPair a b) = getright b

strip :: [(Ports,Int,Ports)] -> [(UVar,Int,UVar)]
strip = map (\(v1,x,v2) -> (getright v1, x, getleft v2))


-- must use bubblesort because the ordering isn't transitive
sortit :: [(UVar,Int,UVar)] -> [(UVar,Int,UVar)]
sortit x = let x' = stupidSort x [] in if x==x' then x else sortit x'
 where
  stupidSort []    x = x
  stupidSort (h:t) x = stupidSort t (stupidInsert h x)

  stupidInsert t []    = [t]
  stupidInsert t@(_,_,t') ((a@(_,_,a')):b) = if cmp' x t' a' == LT
                                             then t:a:b
                                             else a:(stupidInsert t b)
  
  cmp' :: [(UVar,Int,UVar)] -> UVar -> UVar -> Ordering
  cmp' [] a b = EQ -- compare a b
  cmp' ((v1,_,v2):r) a b = if a == v1 && b==v2
                           then LT
                           else if a == v2 && b==v1
                                then GT
                                else cmp' r a b

lookup'' :: Map UVar Int -> UVar -> Int
lookup'' m x = case lookup x m of
                 Nothing -> 0
                 Just y -> y

valuatit :: Map UVar Int -> [(UVar,Int,UVar)] -> Map UVar Int
valuatit m []            = m
valuatit m ((v1,k,v2):r) = valuatit m' r
                            where
                              m'  = insert v2 v2' m
                              v2' = max (lookup'' m v2) (k+(lookup'' m v1))

resolve'k :: UyM () [(Ports,Int,Ports)]
resolve'k = do { k  <- getK
              ; k' <- mapM (\(v1,x,v2) -> do { v1' <- getM v1 ; v2' <- getM v2 ; return (v1',x,v2') }) k
              ; return k'
              }

toTikZ :: GArrowSkeleton m a b -> String
toTikZ g = tikZ m d 0
            where
              (_,_,_,(d,k)) = runU $ do { d <- ga2diag g
                                        ; d' <- resolve' d
                                        ; k' <- resolve'k
                                        ; return (d',k') }
              s = sortit (strip k)
              m = valuatit empty s
toTikZ' :: GArrowSkeleton m a b -> String
toTikZ' g = foldr (\x y -> x++"\\\\\n"++y) [] (map foo s)
             where
               (_,_,_,k) = runU $ ga2diag g >>= resolve' >>= \_ -> resolve'k
               foo (v1,v,v2) = "x_{"++show v1++"} + "++show v++" \\leq x_{"++show v2++"} = " ++ (show $ lookup'' m v2)
               s = sortit (strip k)
               m = valuatit empty s

tikz' :: (forall g a .
                 PGArrow g (GArrowUnit g) a ->
                 (
                   forall b . PGArrow g (GArrowTensor g b b) b) ->
                     PGArrow g (GArrowUnit g) a) -> IO ()
tikz' x = tikz $ optimize $ unG (x (PGArrowD { unG = GAS_const 12 }) (PGArrowD { unG = GAS_merge }) )
main = do putStrLn "hello"
tikz example
     = do putStrLn "\\documentclass{article}"
          putStrLn "\\usepackage[landscape,paperwidth=20in,textheight=19in,paperheight=40in,textwidth=39in]{geometry}"
          putStrLn "\\usepackage{tikz}"
          putStrLn "\\usepackage{amsmath}"
          putStrLn "\\begin{document}"
          putStrLn $ "\\begin{tikzpicture}[every on chain/.style={join=by ->},yscale=-1]"
          putStrLn (toTikZ example)
          putStrLn "\\end{tikzpicture}"
          --putStrLn "\\pagebreak"
          --putStrLn "\\begin{align*}"
          --putStr   (toTikZ' example)
          --putStrLn "\\end{align*}"
          putStrLn "\\end{document}"
