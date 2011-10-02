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
-- | Renders a @GArrowSkeleton@ using TikZ; the result is LaTeX code.
-- You must have lp_solve installed in order for this to work.
--

module GArrowTikZ (tikz)
where
import System.Process
import Prelude hiding ( id, (.), lookup )
import Control.Category
import Control.Monad.State
import GHC.HetMet.GArrow
import Data.List hiding (lookup, insert)
import Data.Map hiding (map, (!))
import Data.Maybe (catMaybes)
import Unify
import GArrowSkeleton
import GArrowPortShape
import GHC.HetMet.Private

------------------------------------------------------------------------------
-- Tracks

--
-- Figuring out the x-coordinates of the boxes is easy, but we'll need
-- to use lp_solve to get a nice layout for the y-coordinates of the
-- wires.  A @Track@ is basically just a y-axis position for one of
-- the horizontal wires in the boxes-and-wires diagram; we will assign
-- a unique Int to each visual element that has a y-coordinate, then
-- generate a big pile of constraints on these y-coordinates and have
-- lp_solve find a solution.
--
type TrackIdentifier = Int

data Tracks = T  TrackIdentifier
            | TU TrackIdentifier  -- a track known to be of unit type
            | TT Tracks Tracks

instance Show Tracks where
 show (T  ti   ) = "(T "++show ti++")"
 show (TU ti   ) = "(TU "++show ti++")"
 show (TT t1 t2) = "(TT "++show t1++" "++show t2++")"

--
-- | TrackPositions maps TrackIdentifiers to actual y-axis positions;
-- this is what lp_solve gives us
-- 
type TrackPositions = TrackIdentifier -> Float

(!) :: TrackPositions -> TrackIdentifier -> Float
tp ! ti = tp ti

-- | get the uppermost TrackIdentifier in a Tracks
uppermost  (T x)    = x
uppermost  (TU x)    = x
uppermost  (TT x y) = uppermost x

-- | get the lowermost TrackIdentifier in a Tracks
lowermost (T x)    = x
lowermost (TU x)    = x
lowermost (TT x y) = lowermost y




------------------------------------------------------------------------------
-- Diagrams

-- | A Diagram is the visual representation of a GArrowSkeleton
data Diagram
  = DiagramComp      Diagram Diagram
  | DiagramBox       Float TrackIdentifier Tracks BoxRenderer Tracks TrackIdentifier
  | DiagramBypassTop Tracks Diagram
  | DiagramBypassBot        Diagram Tracks
  | DiagramLoopTop   Tracks Diagram
  | DiagramLoopBot          Diagram Tracks

-- | get the output tracks of a diagram
getOut :: Diagram -> Tracks
getOut (DiagramComp f g)                     = getOut g
getOut (DiagramBox wid ptop pin q pout pbot)     = pout
getOut (DiagramBypassTop p f)                = TT p (getOut f)
getOut (DiagramBypassBot f p)                = TT (getOut f) p
getOut (DiagramLoopTop t d)                  = case getOut d of { TT z y -> y ; _ -> error "DiagramLoopTop: mismatch" }
getOut (DiagramLoopBot d t)                  = case getOut d of { TT y z -> y ; _ -> error "DiagramLoopBot: mismatch" }

-- | get the input tracks of a diagram
getIn :: Diagram -> Tracks
getIn (DiagramComp f g)                      = getIn f
getIn (DiagramBox wid ptop pin q pout pbot)      = pin
getIn (DiagramBypassTop p f)                 = TT p (getIn f)
getIn (DiagramBypassBot f p)                 = TT (getIn f) p
getIn (DiagramLoopTop t d)                   = case getIn d of { TT z x -> x ; _ -> error "DiagramLoopTop: mismatch" }
getIn (DiagramLoopBot d t)                   = case getIn d of { TT x z -> x ; _ -> error "DiagramLoopBot: mismatch" }

-- | A BoxRenderer is just a routine that, given the dimensions of a
-- boxes-and-wires box element, knows how to spit out a bunch of TikZ
-- code that draws it
type BoxRenderer =
    TrackPositions ->  -- resolves the TrackIdentifiers to actual y-coordinates
    Float          ->  -- x1
    Float          ->  -- y1
    Float          ->  -- x2
    Float          ->  -- y2
    String             -- TikZ code
noRender :: BoxRenderer
noRender _ _ _ _ _ = ""




------------------------------------------------------------------------------
-- Constraints

-- | a constraint (to be dealt with by lp_solve) relates two track identifiers
data Constraint = C TrackIdentifier Ordering TrackIdentifier {- plus -} Float
                | EqualSpace TrackIdentifier TrackIdentifier TrackIdentifier TrackIdentifier

-- instance Show Constraint where
--  show (C t1 LT t2 k s) = "x"++(show t1)++"  = x"++(show t2)++" + "++(show k) ++ ";\n"
--  show (C t1 GT t2 k s) = "x"++(show t1)++"  = x"++(show t2)++" + "++(show k) ++ ";\n"
--  show (C t1 EQ t2 k s) = "x"++(show t1)++"  = x"++(show t2)++" + "++(show k) ++ ";\n"

instance Show Constraint where
 show (C t1 LT t2 k) = "x"++(show t1)++" <= x"++(show t2)++" + "++(show k) ++ ";\n"
 show (C t1 GT t2 k) = "x"++(show t1)++" >= x"++(show t2)++" + "++(show k) ++ ";\n"
 show (C t1 EQ t2 k) = "x"++(show t1)++"  = x"++(show t2)++" + "++(show k) ++ ";\n"
 show (EqualSpace t1a t1b t2a t2b) = "x"++(show t1a)++" = x"++(show t1b)++
                                     " + x"++(show t2a)++" - x"++(show t2b)++ ";\n"

-- | a monad to accumulate constraints and track the largest TrackIdentifier allocated
type ConstraintM a = State (TrackIdentifier,[Constraint]) a

-- | pull the constraints out of the monad
getConstraints :: ConstraintM [Constraint]
getConstraints = do { (_,c) <- get ; return c }

-- | add a constraint
constrain :: TrackIdentifier -> Ordering -> TrackIdentifier {- plus -} -> Float -> ConstraintM ()
constrain t1 ord t2 k = do { (t,c) <- get
                           ; put (t, (C t1 ord t2 k):c)
                           ; return ()
                           }

constrainEqualSpace t1a t1b t2a t2b = do { (t,c) <- get
                                         ; put (t, (EqualSpace t1a t1b t2a t2b):c)
                                         ; return ()
                                         }

-- | simple form for equality constraints
constrainEq (TT t1a t1b) (TT t2a t2b) = do { constrainEq t1a t2a ; constrainEq t1b t2b ; return () }
constrainEq (T  t1     ) (T  t2     ) = constrain t1 EQ t2 0
constrainEq (TU t1     ) (TU t2     ) = constrain t1 EQ t2 0
constrainEq (TU t1     ) (T  t2     ) = constrain t1 EQ t2 0
constrainEq (T  t1     ) (TU t2     ) = constrain t1 EQ t2 0
constrainEq t1 t2                     = error $ "constrainEq mismatch: " ++ show t1 ++ " and " ++ show t2

-- | allocate a TrackIdentifier
alloc1 :: ConstraintM Tracks
alloc1 = do { (t,c) <- get
            ; put (t+1,c)
            ; return (T t)
            }

mkdiag :: GArrowPortShape m () a b -> ConstraintM Diagram
mkdiag (GASPortPassthrough  inp outp m) = error "not supported"
mkdiag (GASPortShapeWrapper inp outp x) = mkdiag' x
 where
 mkdiag' :: GArrowSkeleton (GArrowPortShape m ()) a b -> ConstraintM Diagram
 
 mkdiag' (GAS_comp f g) = do { f' <- mkdiag' f; g' <- mkdiag' g
                             ; constrainEq (getOut f') (getIn g') ; return $ DiagramComp f' g' }
 mkdiag' (GAS_first  f) = do { (top,(TT _ x),bot) <- alloc inp; f' <- mkdiag' f ; constrainBot f' 1 (uppermost x)
                             ; return $ DiagramBypassBot f' x  }
 mkdiag' (GAS_second f) = do { (top,(TT x _),bot) <- alloc inp; f' <- mkdiag' f ; constrainTop (lowermost x) 1 f'
                             ; return $ DiagramBypassTop x f'  }
 mkdiag' (GAS_id      ) = do { (top,    x   ,bot) <- alloc inp ; simpleDiag'        "id" top x x bot        [(x,x)]  "gray!50"    }
 mkdiag' GAS_cancell    = do { (top,(TT x y),bot) <- alloc inp
                             ; let r tp x1 y1 x2 y2 = drawBox x1 y1 x2 y2 "gray!50" "cancell" ++
                                                      drawWires tp x1 y x2 y "black" ++
                                                      drawLine  x1 (tp!lowermost x)  ((x1+x2)/2) (tp!uppermost y) "gray!50" "dashed"
                             ; return $ DiagramBox 2 top (TT x y) r y bot  }
 mkdiag' GAS_cancelr    = do { (top,(TT x y),bot) <- alloc inp
                             ; let r tp x1 y1 x2 y2 = drawBox x1 y1 x2 y2 "gray!50" "cancelr" ++
                                                      drawWires tp x1 x x2 x "black" ++
                                                      drawLine  x1 (tp!uppermost y) ((x1+x2)/2) (tp!lowermost x) "gray!50" "dashed"
                             ; return $ DiagramBox 2 top (TT x y) r x bot  }
 mkdiag' GAS_uncancell  = do { (top,(TT x y),bot) <- alloc outp
                             ; let r tp x1 y1 x2 y2 = drawBox x1 y1 x2 y2 "gray!50" "uncancell" ++
                                                      drawWires tp x1 y x2 y "black" ++
                                                      drawLine  ((x1+x2)/2) (tp!uppermost y) x2 (tp!lowermost x) "gray!50" "dashed"
                             ; return $ DiagramBox 2 top y r (TT x y) bot  }
 mkdiag' GAS_uncancelr  = do { (top,(TT x y),bot) <- alloc outp
                             ; let r tp x1 y1 x2 y2 = drawBox x1 y1 x2 y2 "gray!50" "uncancelr" ++
                                                      drawWires tp x1 x x2 x "black" ++
                                                      drawLine  ((x1+x2)/2) (tp!lowermost x) x2 (tp!uppermost y) "gray!50" "dashed"
                             ; return $ DiagramBox 2 top x r (TT x y) bot  }
 mkdiag' GAS_drop       = do { (top,    x   ,bot) <- alloc inp
                             ; (_,      y   ,_)   <- alloc outp
                             ; constrainEq x y
                             ; simpleDiag   "drop" top x y bot [] }
 mkdiag' (GAS_const i)  = do { (top,    x   ,bot) <- alloc inp
                             ; (_,      y   ,_)   <- alloc outp
                             ; constrainEq x y
                             ; simpleDiag   ("const " ++ show i) top x y bot [] }
 mkdiag' GAS_copy       = do { (top,(TT y z),bot) <- alloc outp
                             ; (_  ,      x ,_)   <- alloc inp
                             ; constrainEqualSpace (lowermost y) (uppermost x) (lowermost x) (uppermost z)
                             ; let r tp x1 y1 x2 y2 = drawBox x1 y1 x2 y2 "gray!50" "copy" ++
                                                      drawWires tp x1 x ((x1+x2)/2) x "black" ++
                                                      drawWires tp ((x1+x2)/2) x x2 y "black" ++
                                                      drawWires tp ((x1+x2)/2) x x2 z "black"
                             ; return $ DiagramBox 2 top x r (TT y z) bot
                             }
 mkdiag' GAS_merge      = do { (top,(TT x y),bot) <- alloc inp 
                             ; simpleDiag     "times" top (TT x y) x bot [] }
 mkdiag' GAS_swap       = do { (top,(TT x y),bot) <- alloc inp
                             ; (top,(TT x' y'),bot) <- alloc outp
                             ; constrainEq (T (lowermost x)) (T (lowermost x'))
                             ; constrainEq (T (uppermost y)) (T (uppermost y'))
                             ; simpleDiag'    "swap"  top (TT x y) (TT x' y') bot [(x,y'),(y,x')] "gray!50" }
 mkdiag' GAS_assoc      =
     do { (top,(TT (TT x y) z),bot) <- alloc inp
        ; let r tp x1 y1 x2 y2
                  = drawBox (x1+0.2*xscale) y1 (x2-0.2*xscale) y2 "white" "assoc" ++
                    drawLine x1 y1 x2 y1 "gray!50" "-" ++
                    drawLine x1 y2 x2 y2 "gray!50" "-" ++
                    drawLine  x1      y1                          x1      ((tp ! uppermost x) - 0.5) "gray!50" "-"++
                    drawLine  x1      ((tp ! uppermost x) - 0.5) (x1+0.2) ((tp ! uppermost x) - 0.5) "gray!50" "-"++
                    drawLine (x1+0.2) ((tp ! uppermost x) - 0.5) (x1+0.2) ((tp ! lowermost y) + 0.5) "gray!50" "-"++
                    drawLine (x1+0.2) ((tp ! lowermost y) + 0.5)  x1      ((tp ! lowermost y) + 0.5) "gray!50" "-"++
                    drawLine  x1      ((tp ! lowermost y) + 0.5)  x1      y2                         "gray!50" "-"++
                    drawLine  x2      y2                          x2      ((tp ! lowermost z) + 0.5) "gray!50" "-"++
                    drawLine  x2      ((tp ! lowermost z) + 0.5) (x2-0.2) ((tp ! lowermost z) + 0.5) "gray!50" "-"++
                    drawLine (x2-0.2) ((tp ! lowermost z) + 0.5) (x2-0.2) ((tp ! uppermost y) - 0.5) "gray!50" "-"++
                    drawLine (x2-0.2) ((tp ! uppermost y) - 0.5)  x2      ((tp ! uppermost y) - 0.5) "gray!50" "-"++
                    drawLine  x2      ((tp ! uppermost y) - 0.5)  x2      y1                         "gray!50" "-"++
                    drawWires tp x1 x x2 x "black" ++
                    drawWires tp x1 y x2 y "black" ++
                    drawWires tp x1 z x2 z "black"
        ; let pin = (TT (TT x y) z)
        ; let pout = (TT x (TT y z))
        ; return $ if draw_assoc then DiagramBox 2 top pin r pout bot else DiagramBox 0 top pin noRender pout bot
        }
 mkdiag' GAS_unassoc    =
     do { (top,(TT x (TT y z)),bot) <- alloc inp
        ; let r tp x1 y1 x2 y2
                  = drawBox (x1+0.2*xscale) y1 (x2-0.2*xscale) y2 "white" "unassoc" ++
                    drawLine x1 y1 x2 y1 "gray!50" "-" ++
                    drawLine x1 y2 x2 y2 "gray!50" "-" ++
                    drawLine  x2      y1                          x2      ((tp ! uppermost x) - 0.5) "gray!50" "-"++
                    drawLine  x2      ((tp ! uppermost x) - 0.5) (x2-0.2) ((tp ! uppermost x) - 0.5) "gray!50" "-"++
                    drawLine (x2-0.2) ((tp ! uppermost x) - 0.5) (x2-0.2) ((tp ! lowermost y) + 0.5) "gray!50" "-"++
                    drawLine (x2-0.2) ((tp ! lowermost y) + 0.5)  x2      ((tp ! lowermost y) + 0.5) "gray!50" "-"++
                    drawLine  x2      ((tp ! lowermost y) + 0.5)  x2      y2                         "gray!50" "-"++
                    drawLine  x1      y2                          x1      ((tp ! lowermost z) + 0.5) "gray!50" "-"++
                    drawLine  x1      ((tp ! lowermost z) + 0.5) (x1+0.2) ((tp ! lowermost z) + 0.5) "gray!50" "-"++
                    drawLine (x1+0.2) ((tp ! lowermost z) + 0.5) (x1+0.2) ((tp ! uppermost y) - 0.5) "gray!50" "-"++
                    drawLine (x1+0.2) ((tp ! uppermost y) - 0.5)  x1      ((tp ! uppermost y) - 0.5) "gray!50" "-"++
                    drawLine  x1      ((tp ! uppermost y) - 0.5)  x1      y1                         "gray!50" "-"++
                    drawWires tp x1 x x2 x "black" ++
                    drawWires tp x1 y x2 y "black" ++
                    drawWires tp x1 z x2 z "black"
        ; let pin = (TT x (TT y z))
        ; let pout = (TT (TT x y) z)
        ; return $ if draw_assoc then DiagramBox 2 top pin r pout bot else DiagramBox 0 top pin noRender pout bot
        }
 mkdiag' (GAS_loopl  f) = do { f' <- mkdiag' f
                             ; l <- allocLoop (case (getIn f') of (TT z _) -> z ; _ -> error "GAS_loopl: mismatch")
                             ; constrainTop (lowermost l) loopgap f'
                             ; return $ DiagramLoopTop l f'  }
 mkdiag' (GAS_loopr  f) = do { f' <- mkdiag' f
                             ; l <- allocLoop (case (getIn f') of (TT _ z) -> z ; _ -> error "GAS_loopr: mismatch")
                             ; constrainBot f' loopgap (uppermost l)
                             ; return $ DiagramLoopBot f' l  }
 mkdiag' (GAS_misc f )  = mkdiag f

 diagramBox :: TrackIdentifier -> Tracks -> BoxRenderer -> Tracks -> TrackIdentifier -> ConstraintM Diagram
 diagramBox ptop pin r pout pbot = do { constrain ptop LT (uppermost pin)  (-1)
                                      ; constrain pbot GT (lowermost pin)  1
                                      ; constrain ptop LT (uppermost pout) (-1)
                                      ; constrain pbot GT (lowermost pout) 1
                                      ; constrain ptop LT pbot (-1)
                                      ; return $ DiagramBox 2 ptop pin r pout pbot
                                      }
 simpleDiag  text ptop pin pout pbot conn = simpleDiag' text ptop pin pout pbot conn "black"
 simpleDiag' text ptop pin pout pbot conn color = diagramBox ptop pin defren pout pbot
  where
   defren tp x1 y1 x2 y2 = drawBox x1 y1 x2 y2 color text ++
                           concat (map (\(x,y) -> drawWires tp x1 x x2 y "black") conn)
   --    ++ wires (x-1) p1  x    "green"
   --    ++ wires  (x+w) p2 (x+w+1) "red"

--draw_assoc = False
--draw_first_second = False
draw_assoc = True
draw_first_second = True

-- constrain that Ports is at least Int units above the topmost portion of Diagram
constrainTop :: TrackIdentifier -> Float -> Diagram -> ConstraintM ()
constrainTop v i (DiagramComp d1 d2)                  = do { constrainTop v i d1 ; constrainTop v i d2 ; return () }
constrainTop v i (DiagramBypassTop p d)               = constrain v LT (uppermost p) (-1 * i)
constrainTop v i (DiagramBypassBot d p)               = constrainTop v (i+1) d
constrainTop v i (DiagramBox wid ptop pin r pout pbot)    = constrain v LT ptop (-1 * i)
constrainTop v i (DiagramLoopTop p d)                 = constrain v LT (uppermost p) (-1 * i)
constrainTop v i (DiagramLoopBot d p)                 = constrainTop v (i+1) d

-- constrain that Ports is at least Int units below the bottommost portion of Diagram
constrainBot :: Diagram -> Float -> TrackIdentifier -> ConstraintM ()
constrainBot (DiagramComp d1 d2)                  i v = do { constrainBot d1 i v ; constrainBot d2 i v ; return () }
constrainBot (DiagramBypassTop p d)               i v = constrainBot d (i+1) v
constrainBot (DiagramBypassBot d p)               i v = constrain v GT (lowermost p) 2
constrainBot (DiagramBox wid ptop pin r pout pbot)    i v = constrain v GT pbot i
constrainBot (DiagramLoopTop p d)                 i v = constrainBot d (i+1) v
constrainBot (DiagramLoopBot d p)                 i v = constrain v GT (lowermost p) 2

-- | The width of a box is easy to calculate
width :: TrackPositions -> Diagram -> Float
width m (DiagramComp d1 d2)               = (width m d1) + 1 + (width m d2)
width m (DiagramBox wid ptop pin x pout pbot) = wid
width m (DiagramBypassTop p d)            = (width m d) + (if draw_first_second then 2 else 0)
width m (DiagramBypassBot d p)            = (width m d) + (if draw_first_second then 2 else 0)
width m (DiagramLoopTop p d)              = (width m d) + 2 + 2 * (loopgap + (m ! lowermost p) - (m ! uppermost p))
width m (DiagramLoopBot d p)              = (width m d) + 2 + 2 * (loopgap + (m ! lowermost p) - (m ! uppermost p))

drawWires :: TrackPositions -> Float -> Tracks -> Float -> Tracks -> String -> String
drawWires tp x1 (TT a b) x2 (TT a' b') color = drawWires tp x1 a x2 a' color ++ drawWires tp x1 b x2 b' color
drawWires tp x1 (T a)    x2 (T a')     color = drawLine x1 (tp!a) x2 (tp!a') color     "-"
drawWires tp x1 (TU a)   x2 (TU a')    color = drawLine x1 (tp!a) x2 (tp!a') "gray!50" "dashed"
drawWires tp _ _ _ _ _                       = error "drawwires fail"

wirecos :: TrackPositions -> Tracks -> [(Float,Bool)]
wirecos tp (TT a b) = wirecos tp a ++ wirecos tp b
wirecos tp (T  a)   = [(tp!a,True)]
wirecos tp (TU a)   = [(tp!a,False)]

wire90 :: Float -> Float -> (Float,Float,Bool) -> String
wire90 x y (y1,y2,b) = drawLine' [(x,y1),(x',y1),(x',y2),(x,y2)] color (style++",rounded corners")
 where
  color = if b then "black" else "gray!50"
  style = if b then "-" else "dashed"
  x'    = x - (y - y1) - loopgap

wire90' x y (y1,y2,b) = drawLine' [(x,y1),(x',y1),(x',y2),(x,y2)] color (style++",rounded corners")
 where
  color = if b then "black" else "gray!50"
  style = if b then "-" else "dashed"
  x'    = x + (y - y1) + loopgap

tikZ :: TrackPositions ->
        Diagram ->
        Float ->                -- horizontal position
        String
tikZ m = tikZ'
 where
  tikZ'  d@(DiagramComp d1 d2)    x = tikZ' d1 x
                                      ++ wires' (x+width m d1) (getOut d1) (x+width m d1+0.5) "black" "->"
                                      ++ wires' (x+width m d1+0.5) (getOut d1) (x+width m d1+1) "black" "-"
                                      ++ tikZ' d2 (x + width m d1 + 1)
  tikZ' d'@(DiagramBypassTop p d) x = if not draw_first_second
                                      then drawWires m x p (x+width m d) p "black" ++ tikZ' d x
                                      else
                                      let top = getTop d' in
                                      let bot = getBot d' in
                                      drawBox  x top (x+width m d') bot "gray!50" "second"
                                      ++ drawWires m x (getIn d) (x+1) (getIn d) "black"
                                      ++ tikZ' d (x+1)
                                      ++ drawWires m (x+1+width m d) (getOut d) (x+1+width m d+1) (getOut d) "black"
                                      ++ drawWires m x p (x+1+width m d+1) p "black"
  tikZ' d'@(DiagramBypassBot d p) x = if not draw_first_second
                                      then drawWires m x p (x+width m d) p "black" ++ tikZ' d x
                                      else
                                      let top = getTop d' in
                                      let bot = getBot d' in
                                      drawBox  x top (x+width m d') bot "gray!50" "first"
                                      ++ drawWires m x (getIn d) (x+1) (getIn d) "black"
                                      ++ tikZ' d (x+1)
                                      ++ drawWires m (x+1+width m d) (getOut d) (x+1+width m d+1) (getOut d) "black"
                                      ++ drawWires m x p (x+1+width m d+1) p "black"
  tikZ' d'@(DiagramLoopTop p d) x   = let top = getTop d' in
                                      let bot = getBot d' in
                                      let gap = loopgap + (m ! lowermost p) - (m ! uppermost p) in
                                      drawBox  x top (x+width m d') bot "gray!50" "loopl"
                                      ++ tikZ' d (x+1+gap)
                                      ++ drawWires m (x+1+gap) p (x+1+gap+width m d) p "black"
                                      ++ let p'   = case getIn d of TT z _ -> z ; _ -> error "DiagramLoopTop: mismatch"
                                             pzip = map (\((y,b),(y',_)) -> (y,y',b)) $ zip (wirecos m p) (reverse $ wirecos m p')
                                         in  concatMap (wire90  (x+1+gap) (m ! lowermost p)) pzip
                                      ++ let p'   = case getOut d of TT z _ -> z ; _ -> error "DiagramLoopTop: mismatch"
                                             pzip = map (\((y,b),(y',_)) -> (y,y',b)) $ zip (wirecos m p) (reverse $ wirecos m p')
                                         in  concatMap (wire90' (x+1+gap+width m d) (m ! lowermost p)) pzip
                                      ++ let rest = case getIn d of TT _ z -> z ; _ -> error "DiagramLoopTop: mismatch"
                                         in  drawWires m x rest (x+1+gap) rest "black"
                                      ++ let rest = case getOut d of TT _ z -> z ; _ -> error "DiagramLoopTop: mismatch"
                                         in  drawWires m (x+1+gap+width m d) rest (x+width m d') rest "black"
  tikZ' d'@(DiagramLoopBot d p) x_  = error "not implemented"
  tikZ' d@(DiagramBox wid ptop pin r pout pbot) x = r m x (m ! ptop) (x + width m d) (m ! pbot)

  wires x1 t x2 c = wires' x1 t x2 c "-"

  wires' :: Float -> Tracks -> Float -> String -> String -> String
  wires' x1 (TT x y) x2 color st = wires' x1 x x2 color st ++ wires' x1 y x2 color st
  wires' x1 (T v)    x2 color st = drawLine x1 (m ! v) x2 (m ! v) color st -- ++ textc ((x1+x2) / 2) (m!v) (show v) "purple"
  wires' x1 (TU v)   x2 color st = drawLine x1 (m ! v) x2 (m ! v) "gray!50" "dashed"

  getTop :: Diagram -> Float
  getTop (DiagramComp d1 d2)        = min (getTop d1) (getTop d2)
  getTop (DiagramBox wid ptop _ _ _ _)  = m ! ptop
  getTop (DiagramBypassTop p d)     = (m ! uppermost p) - 1
  getTop (DiagramBypassBot d p)     = getTop d - 1
  getTop (DiagramLoopTop p d)       = (m ! uppermost p) - 1
  getTop (DiagramLoopBot d p)       = getTop d - 1

  getBot :: Diagram -> Float
  getBot (DiagramComp d1 d2)        = max (getBot d1) (getBot d2)
  getBot (DiagramBox wid _ _ _ _ pbot)  = m ! pbot
  getBot (DiagramBypassTop p d)     = getBot d + 1
  getBot (DiagramBypassBot d p)     = (m ! lowermost p) + 1
  getBot (DiagramLoopTop p d)       = getBot d + 1
  getBot (DiagramLoopBot d p)       = (m ! lowermost p) + 1

-- allocates multiple tracks, adding constraints that they are at least one unit apart
alloc :: PortShape a -> ConstraintM (TrackIdentifier,Tracks,TrackIdentifier)
alloc shape = do { tracks <- alloc' shape
                 ; T ptop <- alloc1
                 ; T pbot <- alloc1
                 ; constrain ptop LT (uppermost tracks) (-1)
                 ; constrain pbot GT (lowermost tracks) 1
                 ; return (ptop,tracks,pbot)
                 }
 where
   alloc' :: PortShape a -> ConstraintM Tracks
   alloc' PortUnit           = do { T x <- alloc1 ; return (TU x) }
   alloc' (PortFree _)       = do { x <- alloc1 ; return x }
   alloc' (PortTensor p1 p2) = do { x1 <- alloc' p1
                                  ; x2 <- alloc' p2
                                  ; constrain (lowermost x1) LT (uppermost x2) (-1)
                                  ; return (TT x1 x2)
                                  }

-- allocates a second set of tracks identical to the first one but constrained only relative to each other (one unit apart)
-- and upside-down
allocLoop :: Tracks -> ConstraintM Tracks
allocLoop (TU _)       = do { T x <- alloc1 ; return (TU x) }
allocLoop (T  _)       = do { x <- alloc1   ; return x }
allocLoop (TT t1 t2)   = do { x1 <- allocLoop t2
                            ; x2 <- allocLoop t1
                            ; constrain (lowermost x1) LT (uppermost x2) (-1)
                            ; return (TT x1 x2)
                            }

do_lp_solve :: [Constraint] -> IO String
do_lp_solve c = do { let stdin = "min: x1;\n" ++ (foldl (++) "" (map show c)) ++ "\n"
                   ; putStrLn stdin
                   ; stdout <- readProcess "lp_solve" [] stdin
                   ; return stdout
                   }

splitWs :: String -> [String]
splitWs s = splitWs' "" s
 where
  splitWs' [] []       = []
  splitWs' acc []      = [acc]
  splitWs' []  (' ':k) = splitWs' [] k
  splitWs' acc (' ':k) = acc:(splitWs' [] k)
  splitWs' acc (x:k)   = splitWs' (acc++[x]) k

lp_solve_to_trackpos :: String -> TrackPositions
lp_solve_to_trackpos s = toTrackPos $ map parse $ catMaybes $ map grab $ lines s
 where
   grab ('x':k) = Just k
   grab _       = Nothing
   parse :: String -> (Int,Float)
   parse s = case splitWs s of
               [a,b] -> (read a, read b)
               _     -> error "parse: should not happen"
   toTrackPos :: [(Int,Float)] -> TrackPositions
   toTrackPos []           tr = 0 -- error $ "could not find track "++show tr
   toTrackPos ((i,f):rest) tr = if (i==tr) then f else toTrackPos rest tr

toTikZ :: GArrowSkeleton m a b -> IO String
toTikZ g = 
    let cm = do { let g' = detectShape g
                ; g'' <- mkdiag g'
                ; return g''
                }
     in do { let (_,constraints) = execState cm (0,[])
           ; lps <- do_lp_solve $ constraints
           ; let m = lp_solve_to_trackpos lps
           ; let d = evalState cm (0,[])
           ; let t = tikZ m d 1
           ; return (t ++ drawWires m 0             (getIn  d) 1             (getIn  d) "black"
                       ++ drawWires m (width m d+1) (getOut d) (width m d+2) (getOut d) "black")
           }
     

tikz :: forall c .
    (forall g .
             (Int -> PGArrow g (GArrowUnit g) Int) ->
             (PGArrow g (GArrowTensor g c c) c) ->
             PGArrow g c c)
     -> IO ()
tikz x = tikz' $ beautify $ optimize $ unG (x (\c -> PGArrowD { unG = GAS_const c }) (PGArrowD { unG = GAS_merge }))

tikz' example
     = do putStrLn "\\documentclass{article}"
          putStrLn "\\usepackage[paperwidth=\\maxdimen,paperheight=\\maxdimen]{geometry}"
          putStrLn "\\usepackage{tikz}"
          putStrLn "\\usepackage{amsmath}"
          putStrLn "\\usepackage[tightpage,active]{preview}"
          putStrLn "\\begin{document}"
          putStrLn "\\setlength\\PreviewBorder{5pt}"
          putStrLn "\\begin{preview}"
          putStrLn $ "\\begin{tikzpicture}[every on chain/.style={join=by ->},yscale=-1]"
          tikz <- toTikZ example
          putStrLn tikz
          putStrLn "\\end{tikzpicture}"
          putStrLn "\\end{preview}"
          --putStrLn "\\pagebreak"
          --putStrLn "\\begin{align*}"
          --putStr   (toTikZ' example)
          --putStrLn "\\end{align*}"
          putStrLn "\\end{document}"

-- Random TikZ routines
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

drawLine' [] color style = ""
drawLine' (xy1:xy) color style =
  "\\path[draw,color="++color++","++style++"] "++
  foldl (\x y -> x ++ " -- " ++ y) (f xy1) (map f xy)
  ++ ";\n"
   where
     f = (\(x,y) -> "("++show (x*xscale)++","++show (y*yscale)++")")

-- | x scaling factor for the entire diagram, since TikZ doesn't scale font sizes
xscale = 1

-- | y scaling factor for the entire diagram, since TikZ doesn't scale font sizes
yscale = 1

-- | extra gap placed between loopback wires and the contents of the loop module
loopgap = 1