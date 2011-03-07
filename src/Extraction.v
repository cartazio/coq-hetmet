(* need this or the Haskell extraction fails *)
Set Printing Width 1300000.

Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Main.
Require Import HaskCoreVars.
Require Import HaskCore.

Open Scope string_scope.
Extraction Language Haskell.

(* I try to reuse Haskell types mostly to get the "deriving Show" aspect *)
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].
Extract Inductive list   => "([])" [ "([])" "(:)" ].
(*Extract Inductive vec    => "([])" [ "([])" "(:)" ].*)
(*Extract Inductive Tree   => "([])" [ "([])" "(:)" ].*)
Extract Inlined Constant map => "Prelude.map".
Extract Inductive string => "Prelude.String" [ "([])" "(:)" ].
Extract Inductive prod   => "(,)" [ "(,)" ].
Extract Inductive sum    => "Prelude.Either" [ "Prelude.Left" "Prelude.Right" ].
Extract Inductive sumbool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive bool    => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive unit    => "()" [ "()" ].
Extract Inlined Constant string_dec => "(==)".
Extract Inlined Constant ascii_dec => "(==)".
Extract Inductive string => "Prelude.String" [ "[]" "(:)" ].

(* adapted from ExtrOcamlString.v *)
Extract Inductive ascii => "Prelude.Char"
[
"{- If this appears, you're using Ascii internals. Please don't -} (\ b0 b1 b2 b3 b4 b5 b6 b7 ->   let f b i = if b then 1 `shiftL` i else 0 in Data.Char.chr (f b0 0 .|. f b1 1 .|. f b2 2 .|. f b3 3 .|. f b4 4 .|. f b5 5 .|. f b6 6 .|. f b7 7))"
]
"{- If this appears, you're using Ascii internals. Please don't -} (\ f c -> let n = Char.code c in let h i = (n .&. (1 `shiftL` i)) /= 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))".
Extract Constant zero  => "'\000'".
Extract Constant one   => "'\001'".
Extract Constant shift => "\ b c -> Data.Char.chr (((Char.code c) `shiftL` 1) .&. 255 .|. if b then 1 else 0)".

Unset Extraction Optimize.
Unset Extraction AutoInline.

Definition coqCoreToStringPass (s:@CoreExpr CoreVar) : string
   := "FIXME".
(*
Definition coqCoreToCorePass (s:CoreExpr CoreVar) : CoreExpr CoreVar
   :=
*)

Extraction "Extraction.hs" coqCoreToStringPass.

