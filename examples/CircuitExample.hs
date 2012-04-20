{-# OPTIONS_GHC -XModalTypes -ddump-types -XNoMonoPatBinds -XMultiParamTypeClasses -XTypeOperators #-}
module CircuitExample
where
import Control.GArrow
import GHC.HetMet.GuestLanguage hiding ((-))
import Control.Category
import Prelude hiding ( id, (.) )

--
-- From the Appendix of Hughes' __Programming with Arrows__
--

class GArrowLoop g (**) u => GArrowCircuit g (**) u b where
  delay :: Bool -> g b b

-- GArrows which can implment LookUp Tables (LUTs)
class GArrow g (**) u => GArrowLUT g (**) u b where
  lut1 :: ( Bool            -> Bool) -> g  b      b
  lut2 :: ((Bool,Bool)      -> Bool) -> g (b,b)   b
  lut3 :: ((Bool,Bool,Bool) -> Bool) -> g (b,b,b) b

nor = lut2 (not.uncurry (||))

flipflop = ga_loopl $ ga_second ga_swap            >>>
                      ga_assoc                     >>>
                      ga_second ga_unassoc         >>>
                      ga_second (ga_first ga_swap) >>>
                      ga_second ga_assoc           >>>
                      ga_unassoc                   >>>
                      ga_first  nor                >>>
                      ga_second nor                >>>
                      ga_first  (delay False)      >>>
                      ga_second (delay True)       >>>
                      ga_copy

edge = ga_copy                  >>>
       ga_first (delay False)   >>>
       lut2 (\(x,y) -> x && (not y))

-- halfAdd :: Arrow arr => arr (Bool,Bool) (Bool,Bool)
-- halfAdd = proc (x,y) -> returnA -< (x&&y, x/=y)

-- fullAdd :: Arrow arr => arr (Bool,Bool,Bool) (Bool,Bool)
-- fullAdd =
--    proc (x,y,c) -> do
--    (c1,s1) <- halfAdd -< (x,y)
--    (c2,s2) <- halfAdd -< (s1,c)
--    returnA -< (c1||c2,s2)
