{-# OPTIONS_GHC -XModalTypes -fflatten -funsafe-skolemize -dcore-lint -XScopedTypeVariables -fsimpleopt-before-flatten -XKindSignatures #-}
module VerilogDemo (oscillator) where

oscillator :: <[ (w,()) ~~> w ]>@a -> <[ (w,(w,())) ~~> w ]>@a -> <[ (w,()) ~~> w ]>@a
oscillator reg xor =
  <[ \input ->
        let output  = ~~xor input delayed
            delayed = ~~reg output
        in output ]>
