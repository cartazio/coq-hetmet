(*********************************************************************************************************************************)
(* HaskGeneral:  Definitions shared by all four representations (Core, Weak, Strong, Proof)                                      *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Coq.Strings.String.
Open Scope nat_scope.

(* all Figure references are to the System FC1 paper *)

(* Figure 1: production T; index is the number of type constructors *)
Variable TyCon      : nat -> Type.               Extract Inlined Constant TyCon => "TyCon.TyCon".

(* Figure 1: production "K" *)
Variable DataCon    :  ∀n, TyCon n               
                                 -> nat          (* number of existential tyvars associated with this datacon *)
                                 -> nat          (* number of coercion variables associated with this datacon *)
                                 -> nat          (* number of value variables (fields) associated with this datacon *)
                                 -> Type.        Extract Inlined Constant DataCon => "DataCon.DataCon".

Variable CoFunConst            : nat -> Type.    (* production "C";  extracts to TyCon.TyCon  *)
Variable TyFunConst            : nat -> Type.    (* production "Sn"; extracts to TyCon.TyCon *)

(* magic TyCons *)
Variable ArrowTyCon            : TyCon 2.        (* the TyCon for (->), the regular old function-space type constructor *)
Variable CoercionTyCon         : TyCon 2.        (* the TyCon for (+>), the coercion type constructor *)
Variable hetMetCodeTypeTyCon   : TyCon 2.        Extract Inlined Constant hetMetCodeTypeTyCon => "TysWiredIn.hetMetCodeTypeTyCon".
Variable Class_                : nat -> Type.    Extract Inlined Constant Class_     => "Class.Class".
Variable classTyCon : ∀ n, Class_ n -> TyCon n.  Extract Inlined Constant classTyCon => "Class.classTyCon".
Variable Note                  : Type.           Extract Inlined Constant Note       => "CoreSyn.Note".
Implicit Arguments DataCon [ [n] ].

(* Figure 7: production κ, ι *)
Inductive Kind : Type := 
  | KindType         : Kind                      (* ★  - the kind of boxed types*)
  | KindTypeFunction : Kind  -> Kind  -> Kind    (* ⇛ *)
  | KindUnliftedType : Kind                      (* not in the paper - this is the kind of unboxed non-tuple types *)
  | KindUnboxedTuple : Kind                      (* not in the paper - this is the kind of unboxed tuples *)
  | KindArgType      : Kind                      (* not in the paper - this is the lub of KindType and KindUnliftedType *)
  | KindOpenType     : Kind                      (* not in the paper - kind of all types (lifted, boxed, whatever) *).

Notation "'★'"   := KindType.
Notation "a ⇛ b" := (KindTypeFunction a b).

Variable tyConToString       : forall n, TyCon n -> string.  Extract Inlined Constant tyConToString         => "outputableToString".
Variable tyFunToString       : ∀ n, TyFunConst n -> string.  Extract Inlined Constant tyFunToString         => "outputableToString".
Variable coFunToString       : ∀ n, CoFunConst n -> string.  Extract Inlined Constant coFunToString         => "outputableToString".
Variable natTostring         : nat->string.                  Extract Inlined Constant natTostring           => "natTostring".


Axiom    tycons_distinct       : ~(ArrowTyCon=hetMetCodeTypeTyCon).
(* GHC provides decision procedures for equality on its primitive types; we tell Coq to blindly trust them *)
Variable tyCon_eq   : forall {k}(n1 n2:TyCon k),  sumbool (n1=n2) (not (n1=n2)).
    Extract Inlined Constant tyCon_eq   => "(==)".
Variable dataCon_eq : forall {n}{tc:TyCon n}{q}{r}{s}(n1 n2:DataCon tc q r s),  sumbool (n1=n2) (not (n1=n2)).
    Extract Inlined Constant dataCon_eq => "(==)".
Axiom    tyCon_eq_reflexive    : forall `(tc:TyCon n),   (tyCon_eq tc tc) = (left _ (refl_equal tc)).
Axiom    dataCon_eq_reflexive  : forall `(tc:@DataCon y z q r p) , (dataCon_eq tc tc) = (left _ (refl_equal tc)).

Instance TyConEqDecidable {n} : EqDecidable (TyCon n) :=
{ eqd_dec            := tyCon_eq
; eqd_dec_reflexive  := tyCon_eq_reflexive
}.

Instance DataConEqDecidable {n}{tc:TyCon n}{a}{b}{c} : EqDecidable (@DataCon _ tc a b c) :=
{ eqd_dec            := dataCon_eq
; eqd_dec_reflexive  := dataCon_eq_reflexive
}.
