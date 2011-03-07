(*********************************************************************************************************************************)
(* HaskWeakVars: types and variables for HaskWeak                                                                               *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import HaskGeneral.
Require Import HaskLiterals.
Require Import HaskCoreVars.
Require Import HaskCoreTypes.

Inductive WeakTypeVar := weakTypeVar : CoreVar -> Kind     -> WeakTypeVar.

Inductive WeakCoercion : Type := weakCoercion : CoreType -> CoreType -> CoreCoercion -> WeakCoercion.

Inductive WeakCoerVar := weakCoerVar : CoreVar -> CoreType -> CoreType -> WeakCoerVar.

Inductive WeakExprVar := weakExprVar : CoreVar -> CoreType -> WeakExprVar.

Inductive WeakVar : Type :=
| WExprVar : WeakExprVar -> WeakVar
| WTypeVar : WeakTypeVar -> WeakVar
| WCoerVar : WeakCoerVar -> WeakVar.

Definition haskLiteralToCoreType lit : CoreType :=
  TyConApp (haskLiteralToTyCon lit) nil.

Definition weakTypeToCoreType (wt:CoreType) : CoreType := wt.

Definition weakTypeToString : CoreType -> string := coreTypeToString ○ weakTypeToCoreType.

(* EqDecidable instances for all of the above *)
Instance CoreTypeVarEqDecidable : EqDecidable WeakTypeVar.
  apply Build_EqDecidable.
  intros.
  destruct v1 as [cv1 k1].
  destruct v2 as [cv2 k2].
  destruct (eqd_dec cv1 cv2); subst.
    destruct (eqd_dec k1 k2); subst.
    left; auto.
    right; intro; apply n; inversion H; subst; auto.
    right; intro; apply n; inversion H; subst; auto.
    Defined.

Instance WeakCoerVarEqDecidable : EqDecidable WeakCoerVar.
  apply Build_EqDecidable.
  intros.
  destruct v1 as [cv1 t1a t1b].
  destruct v2 as [cv2 t2a t2b].
  destruct (eqd_dec cv1 cv2); subst.
    destruct (eqd_dec t1a t2a); subst.
    destruct (eqd_dec t1b t2b); subst.
    left; auto.
    right; intro; apply n; inversion H; subst; auto.
    right; intro; apply n; inversion H; subst; auto.
    right; intro; apply n; inversion H; subst; auto.
    Defined.

Instance WeakExprVarEqDecidable : EqDecidable WeakExprVar.
  apply Build_EqDecidable.
  intros.
  destruct v1 as [cv1 k1].
  destruct v2 as [cv2 k2].
  destruct (eqd_dec cv1 cv2); subst.
    destruct (eqd_dec k1 k2); subst.
    left; auto.
    right; intro; apply n; inversion H; subst; auto.
    right; intro; apply n; inversion H; subst; auto.
    Defined.

Instance WeakVarEqDecidable : EqDecidable WeakVar.
  apply Build_EqDecidable.
  induction v1; destruct v2; try (right; intro q; inversion q; fail) ; auto;
     destruct (eqd_dec w w0); subst.
     left; auto.
     right; intro X; apply n; inversion X; auto.
     left; auto.
     right; intro X; apply n; inversion X; auto.
     left; auto.
     right; intro X; apply n; inversion X; auto.
  Defined.




