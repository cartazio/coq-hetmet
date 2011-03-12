(*********************************************************************************************************************************)
(* HaskWeakTypes: types HaskWeak                                                                                                 *)
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

(* TO DO: mark the TyCon used for hetmet as a "type family" so GHC keeps it fully-applied-at-all-times *)
Variable tyConToCoreTyCon : TyCon -> CoreTyCon.           Extract Inlined Constant tyConToCoreTyCon  => "(\x -> x)".
Variable tyFunToCoreTyCon : TyFun -> CoreTyCon.           Extract Inlined Constant tyFunToCoreTyCon  => "(\x -> x)".
Coercion tyConToCoreTyCon : TyCon >-> CoreTyCon.
Coercion tyFunToCoreTyCon : TyFun >-> CoreTyCon.

Instance TyConToString : ToString TyCon := { toString := tyConToString }.
Instance TyFunToString : ToString TyFun := { toString := tyConToString }.

(* a WeakTypeVar merely wraps a CoreVar and includes its Kind *)
Inductive WeakTypeVar := weakTypeVar : CoreVar -> Kind -> WeakTypeVar.

(*
 * WeakType is much like CoreType, but:
 *   1. avoids mutually-inductive definitions
 *   2. gives special cases for the tycons which have their own typing rules so we can pattern-match on them
 *   3. separates type functions from type constructors, and uses a normal "AppTy" for applying the latter
 *)
Inductive WeakType :=
| WTyVarTy  : WeakTypeVar                                      -> WeakType
| WAppTy    : WeakType            ->                  WeakType -> WeakType
| WTyFunApp : TyFun               ->             list WeakType -> WeakType
| WTyCon    : TyCon                                            -> WeakType
| WFunTyCon :                                                     WeakType    (* never use (WTyCon ArrowCon);    always use this! *)
| WCodeTy   : WeakTypeVar         ->                  WeakType -> WeakType    (* never use the raw tycon *)
| WCoFunTy  : WeakType            -> WeakType      -> WeakType -> WeakType
| WForAllTy : WeakTypeVar         ->                  WeakType -> WeakType
| WClassP   : Class_              ->             list WeakType -> WeakType
| WIParam   : CoreIPName CoreName ->                  WeakType -> WeakType.

(* EqDecidable instances for WeakType *)
Instance WeakTypeVarEqDecidable : EqDecidable WeakTypeVar.
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

(* TO DO: write a proper EqDecidable instance for WeakType and then move the rest of this into HaskWeakToCore *)
Variable ModalBoxTyCon   : TyCon.        Extract Inlined Constant ModalBoxTyCon => "TysWiredIn.hetMetCodeTypeTyCon".
Variable ArrowTyCon      : TyCon.        Extract Constant ArrowTyCon    => "Type.funTyCon".

(* if this is a (WAppTy (WAppTy ... (WTyCon tc) .. ) .. ), return (tc,[...]) *)
Fixpoint isTyConApp (wt:WeakType)(acc:list WeakType) : ??(TyCon * list WeakType) :=
  match wt with
    | WTyCon tc    => Some (tc,acc)
    | WAppTy t1 t2 => isTyConApp t1 (t2::acc)
    | _            => None
  end.

(* messy first-order NON-CAPTURE-AVOIDING substitution on WeakType's *)
Fixpoint replaceWeakTypeVar (te:WeakType)(tv:WeakTypeVar)(tsubst:WeakType) : WeakType :=
  match te with
    | WTyVarTy  tv'            => if eqd_dec tv tv' then tsubst else te
    | WAppTy  t1 t2            => WAppTy (replaceWeakTypeVar t1 tv tsubst) (replaceWeakTypeVar t2 tv tsubst)
    | WForAllTy  tv' t         => if eqd_dec tv tv' then te else WForAllTy tv' (replaceWeakTypeVar t tv tsubst)
    | WCoFunTy t1 t2 t         => WCoFunTy (replaceWeakTypeVar t1 tv tsubst)
                                      (replaceWeakTypeVar t2 tv tsubst) (replaceWeakTypeVar t tv tsubst)
    | WIParam ip ty  => WIParam ip (replaceWeakTypeVar ty tv tsubst)
    | WClassP  c lt => WClassP c ((fix replaceCoreDistinctList (lt:list WeakType) :=
      match lt with
        | nil => nil
        | h::t => (replaceWeakTypeVar h tv tsubst)::(replaceCoreDistinctList t)
      end) lt)
    | WTyFunApp tc lt => WTyFunApp tc ((fix replaceCoreDistinctList (lt:list WeakType) :=
      match lt with
        | nil => nil
        | h::t => (replaceWeakTypeVar h tv tsubst)::(replaceCoreDistinctList t)
      end) lt)
    | WTyCon tc                => WTyCon tc
    | WFunTyCon                => WFunTyCon
    | WModalBoxTyCon           => WModalBoxTyCon
  end.

(* we try to normalize the representation of a type as much as possible before feeding it back to GHCs type-comparison function *)
Definition normalizeWeakType (wt:WeakType) : WeakType := wt.

Fixpoint weakTypeToCoreType' (wt:WeakType) : CoreType :=
  match wt with
    | WTyVarTy  (weakTypeVar v _)     => TyVarTy v
    | WAppTy  t1 t2                   => match (weakTypeToCoreType' t1) with
                                           | TyConApp tc tys => TyConApp tc (app tys ((weakTypeToCoreType' t2)::nil))
                                           | t1'             => AppTy t1' (weakTypeToCoreType' t2)
                                         end
    | WTyCon    tc                    => TyConApp tc nil
    | WTyFunApp tf lt                 => TyConApp tf (map weakTypeToCoreType' lt)
    | WClassP c lt                    => PredTy (ClassP c (map weakTypeToCoreType' lt))
    | WIParam n ty                    => PredTy (IParam n (weakTypeToCoreType' ty))
    | WForAllTy (weakTypeVar wtv _) t => ForAllTy wtv (weakTypeToCoreType' t)
    | WFunTyCon                       => TyConApp ArrowTyCon nil
    | WCodeTy  (weakTypeVar ec _) t   => TyConApp ModalBoxTyCon ((TyVarTy ec)::(weakTypeToCoreType' t)::nil)
    | WCoFunTy t1 t2 t3               => FunTy (PredTy (EqPred (weakTypeToCoreType' t1) (weakTypeToCoreType' t2)))
                                            (weakTypeToCoreType' t3)
  end.

Definition weakTypeToCoreType (wt:WeakType) :=
  weakTypeToCoreType' (normalizeWeakType wt).

Definition compare_weakTypes (w1 w2:WeakType) :=
  if coretype_eq_dec (weakTypeToCoreType w1) (weakTypeToCoreType w2)
    then true
    else false.

(* Coq's "decide equality" can't cope here; we have to cheat for now *)
Axiom compare_weakTypes_axiom : forall w1 w2, if compare_weakTypes w1 w2 then w1=w2 else not (w1=w2).

Instance EqDecidableWeakType : EqDecidable WeakType.
  apply Build_EqDecidable.
  intros.
  set (compare_weakTypes_axiom v1 v2) as x.
  set (compare_weakTypes v1 v2) as y.
  assert (y=compare_weakTypes v1 v2). reflexivity.
  destruct y; rewrite <- H in x.
  left; auto.
  right; auto.
  Defined.

Instance WeakTypeToString : ToString WeakType :=
  { toString := coreTypeToString ○ weakTypeToCoreType }.

