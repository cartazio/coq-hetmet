(*********************************************************************************************************************************)
(* HaskWeakVars: types and variables for HaskWeak                                                                               *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import HaskKinds.
Require Import HaskCoreLiterals.
Require Import HaskCoreVars.
Require Import HaskCoreTypes.
Require Import HaskWeakTypes.

(* TO DO: finish this *)
Inductive WeakCoercion : Type := weakCoercion : Kind -> WeakType -> WeakType -> CoreCoercion -> WeakCoercion.

(* a WeakCoerVar just wraps a CoreVar and tags it with the pair of types amongst which it coerces *)
Inductive WeakCoerVar := weakCoerVar : CoreVar -> Kind -> WeakType -> WeakType -> WeakCoerVar.

(* a WeakExprVar just wraps a CoreVar and tags it with the type of its value *)
Inductive WeakExprVar := weakExprVar : CoreVar -> WeakType -> WeakExprVar.

(* a WeakVar is one of the three sorts *)
Inductive WeakVar : Type :=
| WExprVar : WeakExprVar -> WeakVar
| WTypeVar : WeakTypeVar -> WeakVar
| WCoerVar : WeakCoerVar -> WeakVar.
  Coercion WExprVar : WeakExprVar >-> WeakVar.
  Coercion WTypeVar : WeakTypeVar >-> WeakVar.
  Coercion WCoerVar : WeakCoerVar >-> WeakVar.

Definition weakTypeVarToKind (tv:WeakTypeVar) : Kind :=
  match tv with weakTypeVar _ k => k end.
  Coercion weakTypeVarToKind : WeakTypeVar >-> Kind.

Definition weakVarToCoreVar (wv:WeakVar) : CoreVar :=
  match wv with
  | WExprVar (weakExprVar v _    ) => v
  | WTypeVar (weakTypeVar v _    ) => v
  | WCoerVar (weakCoerVar v _ _ _) => v
 end.
 Coercion weakVarToCoreVar : WeakVar >-> CoreVar.

Definition haskLiteralToWeakType lit : WeakType :=
  WTyCon (haskLiteralToTyCon lit).
  Coercion haskLiteralToWeakType : HaskLiteral >-> WeakType.

Variable coreVarToWeakVar  : CoreVar  -> WeakVar.   Extract Inlined Constant coreVarToWeakVar    => "coreVarToWeakVar".
Variable getTyConTyVars_   : CoreTyCon   -> list CoreVar.  Extract Inlined Constant getTyConTyVars_   => "getTyConTyVars".
Definition tyConTyVars (tc:CoreTyCon) :=
  General.filter (map (fun x => match coreVarToWeakVar x with WTypeVar v => Some v | _ => None end) (getTyConTyVars_ tc)).
  Opaque tyConTyVars.
Definition tyConKind (tc:TyCon) : list Kind :=
  map (fun (x:WeakTypeVar) => x:Kind) (tyConTyVars tc).
Variable tyFunResultKind : CoreTyCon -> Kind. Extract Inlined Constant tyFunResultKind => "tyFunResultKind".
Definition tyFunKind (tc:TyFun) : ((list Kind) * Kind) :=
  ((map (fun (x:WeakTypeVar) => x:Kind) (tyConTyVars tc)) , (tyFunResultKind tc)).

(*
(* EqDecidable instances for all of the above *)
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
*)

Instance WeakVarToString : ToString WeakVar :=
  { toString := fun x => toString (weakVarToCoreVar x) }.