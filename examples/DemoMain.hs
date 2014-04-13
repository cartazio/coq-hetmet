{-# LANGUAGE RankNTypes, FlexibleContexts, NoMonomorphismRestriction, ScopedTypeVariables #-}
import System.IO
import Control.Category
import GArrowTikZ
import GHC.HetMet.Private
import GArrowSkeleton
import GArrowPortShape
import GArrowAssTypes
import BitSerialHardware
import qualified Demo

tikzExample1 =
  ga_copy          >>>
  ga_swap          >>>
  ga_first ga_drop >>>
  ga_cancell

tikzExample2 =
  ga_uncancelr                >>>
  ga_first ga_copy            >>>
  ga_swap                     >>>
  ga_second (ga_first ga_drop >>>
             ga_cancell)      >>>
  ga_cancell

oscillator =
  ga_loopl (ga_first reg >>>
            xor >>>
            ga_copy)

oconst :: Int -> Opaque () a
oconst c = MkOpaque ("{\\large{"++(show c)++"}}") $
           do x <- freshM
              return $ GASPortPassthrough PortUnit (PortFree x) (oconst c)

omult :: Opaque (a,a) a
omult = MkOpaque "{\\large{*}}" $
           do x <- freshM
              return $ GASPortPassthrough (PortTensor (PortFree x) (PortFree x)) (PortFree x) omult

main = do let const c = PGArrowD $ GAS_misc $ oconst c
          let mult    = PGArrowD $ GAS_misc   omult

          sample5 <- toTikZ $ beautify $ optimize $ unG (Demo.sample5 const mult)
          putStrLn $ tikz_header ++ sample5 ++ tikz_footer
          withFile ".build/sample5.tex" WriteMode (\file -> hPutStr file sample5)

          sample1 <- toTikZ $ skelify' tikzExample1
          --putStrLn $ tikz_header ++ sample1 ++ tikz_footer
          withFile ".build/sample1.tex" WriteMode (\file -> hPutStr file sample1)

          sample2 <- toTikZ $ skelify' tikzExample2
          --putStrLn $ tikz_header ++ sample2 ++ tikz_footer
          withFile ".build/sample2.tex" WriteMode (\file -> hPutStr file sample2)

          sample3 <- toTikZ $ skelify'' oscillator
          --putStrLn $ tikz_header ++ sample3 ++ tikz_footer
          withFile ".build/sample3.tex" WriteMode (\file -> hPutStr file sample3)

          sample6 <- toTikZ $ beautify $ optimize $ unG (Demo.sample6 const mult)
          --putStrLn $ tikz_header ++ sample6 ++ tikz_footer
          withFile ".build/sample6.tex" WriteMode (\file -> hPutStr file sample6)
