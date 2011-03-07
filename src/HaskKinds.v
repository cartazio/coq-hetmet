(*********************************************************************************************************************************)
(* HaskKinds:  Definitions shared by all four representations (Core, Weak, Strong, Proof)                                      *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Coq.Strings.String.
Open Scope nat_scope.

Variable Note                : Type.                         Extract Inlined Constant Note       => "CoreSyn.Note".
Variable nat2string          : nat         -> string.        Extract Inlined Constant nat2string            => "nat2string".

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

Instance KindEqDecidable : EqDecidable Kind.
  apply Build_EqDecidable.
  induction v1.
    destruct v2; try (right; intro q; inversion q; fail) ; left ; auto.
    destruct v2; try (right; intro q; inversion q; fail) ; auto.
      destruct (IHv1_1 v2_1); destruct (IHv1_2 v2_2); subst; auto;
      right; intro; subst; inversion H; subst; apply n; auto.
    destruct v2; try (right; intro q; inversion q; fail) ; left ; auto.
    destruct v2; try (right; intro q; inversion q; fail) ; left ; auto.
    destruct v2; try (right; intro q; inversion q; fail) ; left ; auto.
    destruct v2; try (right; intro q; inversion q; fail) ; left ; auto.
  Defined.

