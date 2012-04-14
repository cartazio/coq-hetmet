{-# LANGUAGE MultiParamTypeClasses, TypeOperators, FunctionalDependencies, TypeFamilies, FlexibleContexts, RankNTypes, GADTs, MultiParamTypeClasses, ScopedTypeVariables, FlexibleInstances, UndecidableInstances #-}
-- {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module GArrowVerilog where
import Control.GArrow
import Control.Monad.State
import Data.List (intercalate)
import Control.Category
import Control.Monad ((>=>), (<=<))
import Prelude hiding (id, (.))
import Text.PrettyPrint.HughesPJ
import BitSerialHardware
import GArrowPretty


------------------------------------------------------------------------------
-- Declaration Types (basically (Tree ()))

data DeclType t where
  DeclTypeUnit :: DeclType ()
  DeclTypeWire :: DeclType Wire
  DeclTypePair :: DeclType x -> DeclType y -> DeclType (x,y)

instance Show (DeclType t) where
  show DeclTypeUnit       = "()"
  show DeclTypeWire       = "Wire"
  show (DeclTypePair x y) = case x of
                           DeclTypePair _ _ -> "(" ++ show x ++ ")*" ++ show y
                           _                ->        show x ++  "*" ++ show y

------------------------------------------------------------------------------
-- Identifiers

data Id t where
  IdUnit    :: Id ()
  IdWire    :: String -> Id Wire
  IdPair    :: Id x -> Id y -> Id (x,y)

instance Show (Id t) where
  show IdUnit       = "()"
  show (IdWire n)   = n
  show (IdPair x y) = (show x) ++ "," ++ (show y)

id2shape :: Id t -> DeclType t
id2shape  IdUnit    = DeclTypeUnit
id2shape (IdWire _) = DeclTypeWire
id2shape (IdPair x y) = DeclTypePair (id2shape x) (id2shape y)


------------------------------------------------------------------------------
-- Verilog Writer

class Monad vw => VerilogWriter vw where
  declareWire   :: DeclType t -> vw (Id t)
  gate          :: String -> [Id Wire] -> vw ()

instance MonadState VState m => VerilogWriter m where
  declareWire   DeclTypeUnit      = return IdUnit
  declareWire  (DeclTypePair x y) = do ix <- declareWire x ; iy <- declareWire y ; return $ IdPair ix iy
  declareWire   DeclTypeWire      = do (VState x decls out) <- get
                                       let ids = "wire"++(show x)
                                       put $ VState (x+1) ((text "wire" <+> text ids <> semi):decls) out
                                       return $ IdWire $ ids
  gate name inputs = let output = text name <+> (parens $ hsep $ punctuate comma $ map (text . show) inputs) <> semi
                     in do (VState x decls out) <- get
                           put $ VState x decls (output:out)


------------------------------------------------------------------------------
-- Instance of Verilog Writer

data VState = VState Int [Doc] [Doc]

data V vw x y = V
   { infer :: DeclType x -> DeclType y
   , write :: Id x -> vw (Id y)
   }

instance VerilogWriter vw => Category (V vw) where
  id    = V { infer = id
            , write = return }
  g . f = V { infer = infer g . infer f
            , write = write g <=< write f }



------------------------------------------------------------------------------
-- GArrow implementation

instance VerilogWriter vw => GArrow (V vw) (,) () where
  ga_cancell     = V { infer = \(DeclTypePair DeclTypeUnit sx) -> sx
                     , write = \(IdPair IdUnit x) -> return x }
  ga_cancelr     = V { infer = \(DeclTypePair sx DeclTypeUnit) -> sx
                     , write = \(IdPair x IdUnit) -> return x }
  ga_uncancell   = V { infer = \s -> DeclTypePair DeclTypeUnit s
                     , write = \x -> return (IdPair IdUnit x) }
  ga_uncancelr   = V { infer = \s -> DeclTypePair s DeclTypeUnit
                     , write = \x -> return (IdPair x IdUnit) }
  ga_assoc       = V { infer = \(DeclTypePair (DeclTypePair sx sy) sz) -> DeclTypePair sx (DeclTypePair sy sz)
                     , write = \(IdPair (IdPair x y) z) -> return $ IdPair x (IdPair y z) }
  ga_unassoc     = V { infer = \(DeclTypePair sx (DeclTypePair sy sz)) -> (DeclTypePair (DeclTypePair sx sy) sz)
                     , write = \(IdPair x (IdPair y z)) -> return $ IdPair (IdPair x y) z }
  ga_first     f = V { infer = \(DeclTypePair sx sz) -> DeclTypePair (infer f sx) sz
                     , write = \(IdPair x z) -> do idy <- write f x ; return $ IdPair idy z }
  ga_second    f = V { infer = \(DeclTypePair sz sx) -> DeclTypePair sz (infer f sx)
                     , write = \(IdPair z x) -> do idy <- write f x ; return $ IdPair z idy }

instance VerilogWriter vw => GArrowDrop (V vw) (,) () where
  ga_drop = V { infer = \_ -> DeclTypeUnit
              , write = \_ -> return IdUnit }

instance VerilogWriter vw => GArrowCopy (V vw) (,) () where
  ga_copy = V { infer = \s -> DeclTypePair s s
              , write = \x -> return $ IdPair x x }

instance VerilogWriter vw => GArrowSwap (V vw) (,) () where
  ga_swap = V { infer = \(DeclTypePair x y) -> DeclTypePair y x
              , write = \(IdPair x y) -> return $ IdPair y x }

instance VerilogWriter vw => GArrowLoop (V vw) (,) () where
  ga_loopl f = ga_loopr $ ga_swap >>> f >>> ga_swap
  ga_loopr f = V { infer = \x -> let yz = infer f (DeclTypePair x (case yz of (DeclTypePair y z) -> z))
                                 in (case yz of (DeclTypePair y z) -> y)
                 , write = \idx -> let yz = infer f (DeclTypePair (id2shape idx) (case yz of (DeclTypePair y z) -> z))
                                   in case yz of (DeclTypePair y z) -> do idz  <- declareWire z
                                                                          idyz <- write f (IdPair idx idz)
                                                                          return (case idyz of (IdPair y z) -> y)
                 }

gate1 :: VerilogWriter vw => String -> Id Wire -> vw (Id Wire)
gate1 name x =
  do out <- declareWire DeclTypeWire
     gate name [out,x]
     return out

gate2 :: VerilogWriter vw => String -> Id (Wire,Wire) -> vw (Id Wire)
gate2 name (IdPair x y) =
  do out <- declareWire DeclTypeWire
     gate name [out,x,y]
     return out

gate3 :: VerilogWriter vw => String -> Id (Wire,(Wire,Wire)) -> vw (Id Wire)
gate3 name (IdPair x (IdPair y z)) =
  do out <- declareWire DeclTypeWire
     gate name [out,x,y,z]
     return out

instance VerilogWriter vw => BitSerialHardwarePrimitives (V vw) where
  high        = V { infer = const DeclTypeWire , write = const $ return $ IdWire "1'b1" }
  low         = V { infer = const DeclTypeWire , write = const $ return $ IdWire "1'b0" }
  not         = V { infer = const DeclTypeWire , write = gate1 "not" }
  xor         = V { infer = const DeclTypeWire , write = gate2 "xor" }
  or          = V { infer = const DeclTypeWire , write = gate2 "or" }
  and         = V { infer = const DeclTypeWire , write = gate2 "and" }
  mux2        = V { infer = const DeclTypeWire , write = gate3 "mux2" }
  maj3        = V { infer = const DeclTypeWire , write = gate3 "maj3" }
  reg         = V { infer = const DeclTypeWire , write = gate1 "reg" }
  loop   vals = undefined
  fifo   len  = undefined
  probe  id   = undefined
  oracle id   = undefined


------------------------------------------------------------------------------
-- Examples

oscillator :: BitSerialHardwarePrimitives v => v Wire Wire
oscillator = ga_loopl $ ga_first reg >>> xor >>> ga_copy

sample2 :: MonadState VState m => V m Wire Wire
sample2 = oscillator

sample3 :: V (StateT VState IO) Wire Wire
sample3 = sample2

writeModule moduleName verilog =
  do (VState _ decls out) <- execStateT (write verilog (IdWire "inputWire")) (VState 0 [] [])
     let portNames = [ "inputWire" ]
     let ports = map text portNames
     let out' = vcat [ text "module" <+> text moduleName <> (parens $ sep $ punctuate comma ports)
                     , nest 2 (vcat $ reverse decls)
                     , text ""
                     , nest 2 (vcat $ reverse out)
                     , text "endmodule"
                     ]
     return out'

main :: IO ()
main = do putStrLn $ renderStyle (style{mode=PageMode, ribbonsPerLine=0.1}) $ pprGArrow oscillator
          putStrLn ""
          out' <- writeModule "foo" sample3
          putStrLn $ renderStyle (style{mode=PageMode, ribbonsPerLine=0.1}) out'

submodule :: V vw inputs outputs -> V vw inputs outputs
submodule = undefined

--main = do putStrLn $ show (DeclTypePair (DeclTypePair DeclTypeWire DeclTypeUnit) (DeclTypePair DeclTypeUnit DeclTypeWire))
