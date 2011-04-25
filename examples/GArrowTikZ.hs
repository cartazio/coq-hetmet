{-# OPTIONS_GHC -XModalTypes -XMultiParamTypeClasses -XNoMonoPatBinds -XKindSignatures -XGADTs -XFlexibleContexts -XFlexibleInstances -XTypeOperators -XUndecidableInstances #-}
--module GArrowTikZ
--where
import Prelude hiding ( id, (.), lookup )
import Control.Category
import GHC.HetMet.GArrow
import Data.List hiding (lookup, insert)
import Data.Map hiding (map, (!))
import Unify


{-
TO DO:
    - have "resolve" turn a (Diagram UnifVal) into (Diagram Int)
    - custom rendering
    - bias right now is for all edges to be uppermost; try for bias
      towards smallest nodes?
    - curvy boxes (like XOR gates)
-}


-- a unification value is basically a LISP-ish expression
data UVal =
   UVVar  UVar
 | UVVal  [UVal]

instance Unifiable UVal where
  unify' (UVVal vl1) (UVVal vl2)
      | length vl1 /= length vl2  = error "length mismatch during unification"
      | otherwise                 = foldr mergeU emptyUnifier (map (\(x,y) -> unify x y) $ zip vl1 vl2)
  unify' _ _                      = error "impossible"
  inject                          = UVVar
  project (UVVar v)               = Just v
  project _                       = Nothing
  occurrences (UVVar v)           = [v]
  occurrences (UVVal vl)          = concatMap occurrences vl

-- | Resolves a unification variable; the answer to this query will change if subsequent unifications are performed
getU' :: Unifier UVal -> UVal -> UVal
getU' u (UVVal vl)    = UVVal $ map (getU' u) vl
getU' u x@(UVVar v)   = case Unify.getU u v  of
                                     Nothing -> x
                                     Just x' -> getU' u x'




--
-- | Render a fully-polymorphic GArrow term as a boxes-and-wires diagram using TikZ
--

type Constraints = [(UVal, Int, UVal)]

-- the unification monad
data UyM t a = UyM (([UVar],Unifier UVal,Constraints) -> ([UVar],Unifier UVal,Constraints,a))
instance Monad (UyM t)
 where
  return x      = UyM $ \(i,u,k) -> (i,u,k,x)
  (UyM f) >>= g = UyM $ \(i,u,k) -> let (i',u',k',x) = f (i,u,k) in let UyM g' = g x in g' (i',u',k')


getU        = UyM $ \(i,u,k) -> (i,u,k,u)
getM    v   = UyM $ \(i,u,k) -> (i,u,k,getU' u v)
occursU v x = UyM $ \(i,u,k) -> (i,u,k,occurs u v x)
unifyM :: Eq t => UVal -> UVal -> UyM t ()
unifyM v1 v2 = UyM $ \(i,u,k) -> (i,mergeU u (unify v1 v2),k,())
freshU :: UyM t UVar
freshU = UyM $ \(i:is,u,k) -> (is,u,k,i)
constrain :: UVal -> Int -> UVal -> UyM t ()
constrain v1 d v2 = UyM $ \(i,u,k) -> (i,u,((v1,d,v2):k),())
getK :: UyM t [(UVal, Int, UVal)]
getK = UyM $ \(i,u,k) -> (i,u,k,k)
runU :: UyM t a -> ([UVar],Unifier UVal,Constraints,a)
runU (UyM f) = (f (uvarSupply,emptyUnifier,[]))

data GArrowTikZ :: * -> * -> *
 where
  TikZ_id        ::                                     GArrowTikZ x x
  TikZ_comp      :: GArrowTikZ y z -> GArrowTikZ x y -> GArrowTikZ x z
  TikZ_first     :: GArrowTikZ x y                   -> GArrowTikZ (x**z)  (y**z)
  TikZ_second    :: GArrowTikZ x y                   -> GArrowTikZ (z**x)  (z**y)
  TikZ_cancell   ::                                     GArrowTikZ (()**x) x
  TikZ_cancelr   ::                                     GArrowTikZ (x**()) x
  TikZ_uncancell ::                                     GArrowTikZ x (()**x)
  TikZ_uncancelr ::                                     GArrowTikZ x (x**())
  TikZ_assoc     ::                                     GArrowTikZ ((x**y)**z) (x**(y**z))
  TikZ_unassoc   ::                                     GArrowTikZ (x**(y**z)) ((x**y)**z)
  TikZ_drop      ::                                     GArrowTikZ x         ()
  TikZ_copy      ::                                     GArrowTikZ x         (x**x)
  TikZ_swap      ::                                     GArrowTikZ (x**y)     (y**x)
  TikZ_merge     ::                                     GArrowTikZ (x**y)     z
  TikZ_loopl     ::           GArrowTikZ (x**z) (y**z) -> GArrowTikZ x y
  TikZ_loopr     ::           GArrowTikZ (z**x) (z**y) -> GArrowTikZ x y

--
-- Technically this instance violates the laws (and RULEs) for
-- Control.Category; the compiler might choose to optimize (f >>> id)
-- into f, and this optimization would produce a change in behavior
-- below.  In practice this means that the user must be prepared for
-- the rendered TikZ diagram to be merely *equivalent to* his/her
-- term, rather than structurally exactly equal to it.
--
instance Category GArrowTikZ where
  id           = TikZ_id
  (.)          = TikZ_comp

instance GArrow GArrowTikZ (**) () where
  ga_first     = TikZ_first
  ga_second    = TikZ_second
  ga_cancell   = TikZ_cancell
  ga_cancelr   = TikZ_cancelr
  ga_uncancell = TikZ_uncancell
  ga_uncancelr = TikZ_uncancelr
  ga_assoc     = TikZ_assoc
  ga_unassoc   = TikZ_unassoc

instance GArrowDrop GArrowTikZ (**) () where
  ga_drop      = TikZ_drop

instance GArrowCopy GArrowTikZ (**) () where
  ga_copy      = TikZ_copy

instance GArrowSwap GArrowTikZ (**) () where
  ga_swap      = TikZ_swap

instance GArrowLoop GArrowTikZ (**) () where
  ga_loopl     = TikZ_loopl
  ga_loopr     = TikZ_loopr

name :: GArrowTikZ a b -> String
name TikZ_id              = "id"
name (TikZ_comp      _ _) = "comp"
name (TikZ_first     _  ) = "first"
name (TikZ_second    _  ) = "second"
name TikZ_cancell         = "cancell"
name TikZ_cancelr         = "cancelr"
name TikZ_uncancell       = "uncancell"
name TikZ_uncancelr       = "uncancelr"
name TikZ_drop            = "drop"
name TikZ_copy            = "copy"
name TikZ_swap            = "swap"
name (TikZ_loopl     _ )  = "loopl"
name (TikZ_loopr     _ )  = "loopr"
name TikZ_assoc           = "assoc"
name TikZ_unassoc         = "unassoc"

fresh1 :: UyM () Ports
fresh1 = do { x <- freshU
            ; return $ UVVar x
            }

fresh2 :: UyM () (Ports,Ports)
fresh2 = do { x <- freshU
            ; y <- freshU
            ; constrain (UVVar x) 1 (UVVar y)
            ; return $ (UVVar x,UVVar y)
            }

fresh3 :: UyM () (Ports,Ports,Ports)
fresh3 = do { x <- freshU
            ; y <- freshU
            ; z <- freshU
            ; constrain (UVVar x) 1 (UVVar y)
            ; constrain (UVVar y) 1 (UVVar z)
            ; return $ (UVVar x,UVVar y,UVVar z)
            }

fresh4 :: UyM () (Ports,Ports,Ports,Ports)
fresh4 = do { x1 <- freshU
            ; x2 <- freshU
            ; x3 <- freshU
            ; x4 <- freshU
            ; constrain (UVVar x1) 1 (UVVar x2)
            ; constrain (UVVar x2) 1 (UVVar x3)
            ; constrain (UVVar x3) 1 (UVVar x4)
            ; return $ (UVVar x1,UVVar x2,UVVar x3,UVVar x4)
            }

fresh5 :: UyM () (Ports,Ports,Ports,Ports,Ports)
fresh5 = do { x1 <- freshU
            ; x2 <- freshU
            ; x3 <- freshU
            ; x4 <- freshU
            ; x5 <- freshU
            ; constrain (UVVar x1) 1 (UVVar x2)
            ; constrain (UVVar x2) 1 (UVVar x3)
            ; constrain (UVVar x3) 1 (UVVar x4)
            ; constrain (UVVar x4) 1 (UVVar x5)
            ; return $ (UVVar x1,UVVar x2,UVVar x3,UVVar x4,UVVar x5)
            }




example = ga_first ga_drop >>> ga_cancell >>> ga_first id >>> ga_swap >>> ga_first id >>> TikZ_merge
--example :: forall x y z. forall g. (GArrow g (,) (), GArrowCopy g (,) (), GArrowSwap g (,) ()) => g x ((x,x),x)
--example = ga_copy >>> ga_second ga_copy >>> ga_second (ga_first id) >>> ga_unassoc >>> ga_first ga_swap
--example = ga_copy >>> ga_second ga_copy >>> ga_second (ga_second id) >>> ga_unassoc >>> ga_first id >>> ga_first ga_swap
--example :: forall x. forall g. (GArrow g (,) (), GArrowCopy g (,) (), GArrowSwap g (,) ()) => g x x
--example = id >>> id

data Diagram p = DiagramComp      (Diagram p) (Diagram p)
               | DiagramPrim      String p p p p (String -> Int -> Int -> Int -> p -> p -> Int -> String)
               | DiagramBypassTop p (Diagram p)
               | DiagramBypassBot (Diagram p) p
               -- | DiagramLoopTop   Diagram
               -- | DiagramLoopBot   Diagram

type Ports = UVal

getOut :: Diagram Ports -> Ports
getOut (DiagramComp f g)                     = getOut g
getOut (DiagramPrim s ptop pin pout pbot _)  = pout
getOut (DiagramBypassTop p f)                = UVVal [p, (getOut f)]
getOut (DiagramBypassBot f p)                = UVVal [(getOut f), p]

getIn :: Diagram Ports -> Ports
getIn (DiagramComp f g)                      = getIn f
getIn (DiagramPrim s ptop pin pout pbot _)   = pin
getIn (DiagramBypassTop p f)                 = UVVal [p, (getIn f)]
getIn (DiagramBypassBot f p)                 = UVVal [(getIn f), p]

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

ga2diag :: GArrowTikZ a b -> UyM () (Diagram Ports)
ga2diag (TikZ_id           ) = do { (top,x,bot) <- fresh3 ; return $ DiagramPrim "id" top x x bot defren }
ga2diag (TikZ_comp      g f) = do { f' <- ga2diag f
                                  ; g' <- ga2diag g
                                  ; unifyM (getOut f') (getIn g')
                                  ; return $ DiagramComp f' g' }
ga2diag (TikZ_first  f)=do { x <- fresh1; f' <- ga2diag f ; constrainBot f' 1 x  ; return $ DiagramBypassBot f' x  }
ga2diag (TikZ_second f)=do { x <- fresh1; f' <- ga2diag f ; constrainTop x  1 f' ; return $ DiagramBypassTop x f'  }
ga2diag TikZ_cancell  = do { (top,x,y  ,bot) <- fresh4  ; return $ DiagramPrim   "cancell" top (UVVal [x,y]) y bot defren }
ga2diag TikZ_cancelr  = do { (top,x,y  ,bot) <- fresh4  ; return $ DiagramPrim   "cancelr" top (UVVal [x,y]) x bot defren }
ga2diag TikZ_uncancell= do { (top,x,y  ,bot) <- fresh4  ; return $ DiagramPrim "uncancell" top y (UVVal [x,y]) bot defren }
ga2diag TikZ_uncancelr= do { (top,x,y  ,bot) <- fresh4  ; return $ DiagramPrim "uncancelr" top x (UVVal [x,y]) bot defren }
ga2diag TikZ_drop     = do { (top,x    ,bot) <- fresh3  ; return $ DiagramPrim      "drop" top x x bot defren }
ga2diag TikZ_copy     = do { (top,x,y,z,bot) <- fresh5
                           ; return $ DiagramPrim      "copy" top y (UVVal [x,z]) bot defren }
ga2diag TikZ_merge    = do { (top,x,y,z,bot) <- fresh5
                           ; return $ DiagramPrim      "merge" top (UVVal [x,z]) y bot defren }
ga2diag TikZ_swap     = do { (top,x,y  ,bot) <- fresh4
                           ; return $ DiagramPrim      "swap" top (UVVal [x,y]) (UVVal [x,y]) bot defren }
ga2diag TikZ_assoc    = do { (top,x,y,z,bot) <- fresh5
                           ; return $ DiagramPrim  "assoc" top (UVVal [UVVal [x,y],z])(UVVal [x,UVVal [y,z]]) bot defren }
ga2diag TikZ_unassoc  = do { (top,x,y,z,bot) <- fresh5
                           ; return $ DiagramPrim "unassoc" top (UVVal [x,UVVal [y,z]])(UVVal [UVVal [x,y],z]) bot defren }
ga2diag (TikZ_loopl f) = error "not implemented"
ga2diag (TikZ_loopr f) = error "not implemented"

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
                                      ++ drawLine x (top+1) (x+width d') (top+1) "black" "->"
                                      ++ wires x (getIn d) (x+1) "black"
                                      ++ tikZ' d (x+1)
                                      ++ wires (x+1+width d) (getOut d) (x+1+width d+1) "black"
  tikZ' d'@(DiagramBypassBot d p) x = let top = getTop d' in
                                      let bot = getBot d' in
                                      drawBox  x top (x+width d') bot "gray!50" "first"
                                      ++ drawLine x (bot-1) (x+width d') (bot-1) "black" "->"
                                      ++ wires x (getIn d) (x+1) "black"
                                      ++ tikZ' d (x+1)
                                      ++ wires (x+1+width d) (getOut d) (x+1+width d+1) "black"
  tikZ'  d@(DiagramPrim s (UVVar top) p1 p2 (UVVar bot) r)  x = r s x (width d) (m ! top) p1 p2 (m ! bot)

  wires :: Int -> Ports -> Int -> String -> String
  wires x1 (UVVar v)    x2 color = drawLine x1 (m ! v) x2 (m ! v) color "->"
                                  -- ++ textc ((x1+x2) `div` 2) (m!v) (show v) "purple"
  wires x1 (UVVal vl) x2 color = foldr (\x y -> x ++ " " ++ y) [] (map (\v -> wires x1 v x2 color) vl)

  getTop :: Diagram Ports -> Int
  getTop (DiagramComp d1 d2)                = min (getTop d1) (getTop d2)
  getTop (DiagramBypassTop p d)             = (m ! getleft p) - 1
  getTop (DiagramBypassBot d p)             = getTop d - 1
  getTop (DiagramPrim s (UVVar ptop) _ _ _ _)  = m ! ptop

  getBot :: Diagram Ports -> Int
  getBot (DiagramComp d1 d2)                = max (getBot d1) (getBot d2)
  getBot (DiagramBypassTop p d)             = getBot d + 1
  getBot (DiagramBypassBot d p)             = (m ! getright p) + 1
  getBot (DiagramPrim s _ _ _ (UVVar pbot) _)  = m ! pbot

resolve' (DiagramComp d1 d2)    = do { d1' <- resolve' d1 ; d2' <- resolve' d2 ; return $ DiagramComp d1' d2'    }
resolve' (DiagramBypassTop p d) = do { p'  <- getM p     ; d'  <- resolve' d  ; return $ DiagramBypassTop p' d' }
resolve' (DiagramBypassBot d p) = do { p'  <- getM p     ; d'  <- resolve' d  ; return $ DiagramBypassBot d' p' }
resolve' (DiagramPrim s ptop pin pout pbot r) 
    = do { ptop' <- getM ptop
         ; pbot' <- getM pbot
         ; pin'  <- getM pin
         ; pout' <- getM pout
         ; return $ DiagramPrim s ptop' pin' pout' pbot' r }

getleft (UVVar   v)  = v
getleft (UVVal  vl) = getleft (head vl)

getright (UVVar   v)  = v
getright (UVVal  vl) = getright (last vl)

strip :: [(Ports,Int,Ports)] -> [(UVar,Int,UVar)]
strip = map (\(v1,x,v2) -> (getright v1, x, getleft v2))


-- must use bubblesort because the ordering isn't transitive
sortit :: [(UVar,Int,UVar)] -> [(UVar,Int,UVar)]
sortit x = stupidSort x []
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

toTikZ :: GArrowTikZ a b -> String
toTikZ g = tikZ m d 0
            where
              (_,_,_,(d,k)) = runU $ do { d <- ga2diag g
                                        ; d' <- resolve' d
                                        ; k' <- resolve'k
                                        ; return (d',k') }
              s = sortit (strip k)
              m = valuatit empty s
toTikZ' :: GArrowTikZ a b -> String
toTikZ' g = foldr (\x y -> x++"\\\\\n"++y) [] (map foo s)
             where
               (_,_,_,k) = runU $ ga2diag g >>= resolve' >>= \_ -> resolve'k
               foo (v1,v,v2) = "x_{"++show v1++"} + "++show v++" \\leq x_{"++show v2++"} = " ++ (show $ lookup'' m v2)
               s = sortit (strip k)
               m = valuatit empty s

main = do putStrLn "\\documentclass{article}"
          putStrLn "\\usepackage[landscape,paperheight=20in,textwidth=19in]{geometry}"
          putStrLn "\\usepackage{tikz}"
          putStrLn "\\usepackage{amsmath}"
          putStrLn "\\begin{document}"
          putStrLn $ "\\begin{tikzpicture}[every on chain/.style={join=by ->},yscale=-1]"
          putStrLn (toTikZ example)
          putStrLn "\\end{tikzpicture}"
--          putStrLn "\\begin{align*}"
--          putStr   (toTikZ' example)
--          putStrLn "\\end{align*}"
          putStrLn "\\end{document}"
