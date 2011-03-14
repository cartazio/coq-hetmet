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
Extract Inductive ascii => "Prelude.Char" [ "bin2ascii" ] "bin2ascii'".
Extract Constant zero   => "'\000'".
Extract Constant one    => "'\001'".
Extract Constant shift  => "shiftAscii".

Unset Extraction Optimize.
Unset Extraction AutoInline.

Variable Prelude_error : forall {A}, string -> A.   Extract Inlined Constant Prelude_error => "Prelude.error".

Section core2proof.
  Context (ce:@CoreExpr CoreVar).

  Definition Γ : TypeEnv := nil.

  Definition Δ : CoercionEnv Γ := nil.

  Definition φ : TyVarResolver Γ :=
    fun cv => Error ("unbound tyvar: " +++ (cv:CoreVar)).
    (*fun tv => error ("tried to get the representative of an unbound tyvar:" +++ (getCoreVarOccString tv)).*)

  Definition ψ : CoVarResolver Γ Δ :=
    fun cv => Error ("tried to get the representative of an unbound covar!" (*+++ (getTypeVarOccString cv)*)).

  (* We need to be able to resolve unbound exprvars, but we can be sure their types will have no
   * free tyvars in them *)
  Definition ξ (cv:CoreVar) : LeveledHaskType Γ ★ :=
    match coreVarToWeakVar cv with
      | WExprVar wev => match weakTypeToType'' φ wev ★ with
                          | Error s => Prelude_error ("Error in top-level xi: " +++ s)
                          | OK    t => t @@ nil
                        end
      | WTypeVar _   => Prelude_error "top-level xi got a type variable"
      | WCoerVar _   => Prelude_error "top-level xi got a coercion variable"
    end.

  Definition header : string :=
    "\documentclass[9pt]{article}"+++eol+++
    "\usepackage{amsmath}"+++eol+++
    "\usepackage{amssymb}"+++eol+++
    "\usepackage{proof}"+++eol+++
    "\usepackage{mathpartir}   % http://cristal.inria.fr/~remy/latex/"+++eol+++
    "\usepackage{trfrac}       % http://www.utdallas.edu/~hamlen/trfrac.sty"+++eol+++
    "\def\code#1#2{\Box_{#1} #2}"+++eol+++
    "\usepackage[paperwidth=200in,centering]{geometry}"+++eol+++
    "\usepackage[displaymath,tightpage,active]{preview}"+++eol+++
    "\begin{document}"+++eol+++
    "\begin{preview}"+++eol.

  Definition footer : string :=
    eol+++"\end{preview}"+++
    eol+++"\end{document}"+++
    eol.

  Definition handleExpr' (ce:@CoreExpr CoreVar) : ???string :=
    addErrorMessage ("input CoreSyn: " +++ ce)
    (addErrorMessage ("input CoreType: " +++ coreTypeOfCoreExpr ce) (
      coreExprToWeakExpr ce >>= fun we =>
        addErrorMessage ("WeakExpr: " +++ we)
          ((addErrorMessage ("CoreType of WeakExpr: " +++ coreTypeOfCoreExpr (weakExprToCoreExpr we))
            ((weakTypeOfWeakExpr we) >>= fun t =>
              (addErrorMessage ("WeakType: " +++ t)
                ((weakTypeToType'' φ t ★) >>= fun τ =>
                  addErrorMessage ("HaskType: " +++ τ)
                  ((weakExprToStrongExpr Γ Δ φ ψ ξ τ nil we) >>= fun e =>
                    OK (eol+++"$$"+++ nd_ml_toLatex (@expr2proof _ _ _ _ _ _ e)+++"$$"+++eol)
                  )))))))).

  Definition handleExpr (ce:@CoreExpr CoreVar) : string :=
    match handleExpr' ce with
      | OK x => x
      | Error s => Prelude_error s
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

