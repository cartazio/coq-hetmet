(*********************************************************************************************************************************)
(* ExtractionMain: just the "Extract" command                                                                                    *)
(*********************************************************************************************************************************)

(* need this or the Haskell extraction fails *)
Set Printing Width 1300000.
Require Import ExtractionMain.

(*Set Extraction Optimize.*)
(*Set Extraction AutoInline.*)
Extraction "Extraction.hs" coqPassCoreToString coqPassCoreToCore.

