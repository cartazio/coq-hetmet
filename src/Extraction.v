(* need this or the Haskell extraction fails *)
Set Printing Width 1300000.

Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Require Import Preamble.
Require Import General.

Require Import NaturalDeduction.
Require Import NaturalDeductionToLatex.

Require Import HaskKinds.
Require Import HaskCoreLiterals.
Require Import HaskCoreVars.
Require Import HaskCoreTypes.
Require Import HaskCore.
Require Import HaskWeakVars.
Require Import HaskWeakTypes.
Require Import HaskWeak.
Require Import HaskStrongTypes.
Require Import HaskStrong.
Require Import HaskProof.
Require Import HaskCoreToWeak.
Require Import HaskWeakToStrong.
Require Import HaskStrongToProof.
Require Import HaskProofToStrong.
Require Import HaskProofToLatex.
Require Import HaskStrongToWeak.
Require Import HaskWeakToCore.

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

Axiom fail : forall {A}, string -> A. 
  Extract Inlined Constant fail => "Prelude.error".

Section core2proof.
  Context (ce:@CoreExpr CoreVar).

  Definition Γ : TypeEnv := nil.

  Definition Δ : CoercionEnv Γ := nil.

  Definition φ : CoreVar->HaskTyVar Γ :=
    fun cv => (fun TV env => fail "unbound tyvar").
    (*fun tv => error ("tried to get the representative of an unbound tyvar:" +++ (getCoreVarOccString tv)).*)

  Definition ψ : CoreVar->HaskCoVar nil Δ
    := fun cv => fail ("tried to get the representative of an unbound covar!" (*+++ (getTypeVarOccString cv)*)).

  (* We need to be able to resolve unbound exprvars, but we can be sure their types will have no
   * free tyvars in them *)
  Definition ξ : WeakExprVar -> WeakType * list WeakTypeVar
    := fun (v:WeakExprVar) => ((v:WeakType),nil).

  Definition header : string :=
    "\documentclass[9pt]{article}"+++eol+++
    "\usepackage{amsmath}"+++eol+++
    "\usepackage{amssymb}"+++eol+++
    "\usepackage{proof}"+++eol+++
    "\usepackage{mathpartir}"+++eol+++
    "\usepackage{trfrac}"+++eol+++
    "\def\code#1#2{\Box_{#1} #2}"+++eol+++
    "\usepackage[paperwidth=20in,centering]{geometry}"+++eol+++
    "\usepackage[displaymath,tightpage,active]{preview}"+++eol+++
    "\begin{document}"+++eol+++
    "\begin{preview}"+++eol.

  Definition footer : string :=
    eol+++"\end{preview}"+++
    eol+++"\end{document}"+++
    eol.

  Definition handleExpr (ce:@CoreExpr CoreVar) : string :=
    match coreExprToWeakExpr ce with
      | Error s => fail ("unable to convert GHC Core expression into Coq HaskWeak expression due to:\n  "+++s)
      | OK me   =>
        match weakExprToStrongExpr (*(makeClosedExpression me)*) me Γ Δ φ ψ ξ nil with
          | Indexed_Error  s  => fail ("unable to convert HaskWeak to HaskStrong due to:\n  "+++s)
          | Indexed_OK    τ e => match e with
                                   | Error s => fail ("unable to convert HaskWeak to HaskStrong due to:\n  "+++s)
                                   | OK e'   =>
                                     eol+++"$$"+++
                                     nd_ml_toLatex (@expr2proof _ _ _ _ _ _ e')+++
                                     "$$"+++eol
                                 end
        end
    end.

  Definition handleBind (bind:@CoreBind CoreVar) : string :=
    match bind with
      | CoreNonRec _ e => handleExpr e
      | CoreRec    lbe => fold_left (fun x y => x+++eol+++eol+++y) (map (fun x => handleExpr (snd x)) lbe) ""
    end.

  Definition coqPassCoreToString (lbinds:list (@CoreBind CoreVar)) : string :=
    header +++
    (fold_left (fun x y => x+++eol+++eol+++y) (map handleBind lbinds) "")
    +++ footer.

  Definition coqPassCoreToCore (lbinds:list (@CoreBind CoreVar)) : list (@CoreBind CoreVar) :=
    lbinds.

End core2proof.

Extraction "Extraction.hs" coqPassCoreToString coqPassCoreToCore.

