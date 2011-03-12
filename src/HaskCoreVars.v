(*********************************************************************************************************************************)
(* HaskCoreVars: basically GHC's Var.Var imported into Coqland                                                                   *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Coq.Strings.String.

(* GHC uses a single type for expression variables, type variables, and coercion variables; this is that type *)
Variable CoreVar          : Type.                                               Extract Inlined Constant CoreVar    => "Var.Var".
Variable coreVar_eq       : forall (a b:CoreVar), sumbool (a=b) (not (a=b)).    Extract Inlined Constant coreVar_eq => "(==)".
Variable coreVarToString  : CoreVar      -> string.  Extract Inlined Constant coreVarToString         => "outputableToString".
Axiom    coreVar_eq_refl  : forall v, (coreVar_eq v v) = (left _ (refl_equal v)).
Instance CoreVarEqDecidable : EqDecidable CoreVar := { eqd_dec            := coreVar_eq }.
Instance CoreVarToString : ToString CoreVar :=
  { toString := coreVarToString }.
