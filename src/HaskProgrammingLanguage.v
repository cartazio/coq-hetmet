(*********************************************************************************************************************************)
(* HaskProgrammingLanguage:                                                                                                      *)
(*                                                                                                                               *)
(*    System FC^\alpha is a ProgrammingLanguage.                                                                                 *)
(*                                                                                                                               *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import NaturalDeduction.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Algebras_ch4.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.
Require Import ProductCategories_ch1_6_1.
Require Import OppositeCategories_ch1_6_2.
Require Import Enrichment_ch2_8.
Require Import Subcategories_ch7_1.
Require Import NaturalTransformations_ch7_4.
Require Import NaturalIsomorphisms_ch7_5.
Require Import MonoidalCategories_ch7_8.
Require Import Coherence_ch7_8.

Require Import HaskKinds.
Require Import HaskCoreTypes.
Require Import HaskLiteralsAndTyCons.
Require Import HaskStrongTypes.
Require Import HaskProof.
Require Import NaturalDeduction.
Require Import NaturalDeductionCategory.

Require Import HaskStrongTypes.
Require Import HaskStrong.
Require Import HaskProof.
Require Import HaskStrongToProof.
Require Import HaskProofToStrong.
Require Import ProgrammingLanguage.

Open Scope nd_scope.

(* The judgments any specific Γ,Δ form a category with proofs as morphisms *)
Section HaskProgrammingLanguage.

  Context (ndr_systemfc:@ND_Relation _ Rule).

  Context Γ (Δ:CoercionEnv Γ).

  
  Definition JudgΓΔ := prod (Tree ??(LeveledHaskType Γ ★)) (Tree ??(LeveledHaskType Γ ★)).

  Definition RuleΓΔ : Tree ??JudgΓΔ -> Tree ??JudgΓΔ -> Type :=
    fun h c =>
      Rule
      (mapOptionTree (fun j => Γ > Δ > fst j |- snd j) h)
      (mapOptionTree (fun j => Γ > Δ > fst j |- snd j) c).

  Definition SystemFCa_cut : forall a b c, ND RuleΓΔ ([(a,b)],,[(b,c)]) [(a,c)].
    intros.
    destruct b.
    destruct o.
    destruct c.
    destruct o.

    (* when the cut is a single leaf and the RHS is a single leaf: *)
    (*
    eapply nd_comp.
      eapply nd_prod.
      apply nd_id.
      eapply nd_rule.
      set (@org_fc) as ofc.
      set (RArrange Γ Δ _ _ _ (RuCanL [l0])) as rule.
      apply org_fc with (r:=RArrange _ _ _ _ _ (RuCanL [_])).
      auto.
      eapply nd_comp; [ idtac | eapply nd_rule; apply org_fc with (r:=RArrange _ _ _ _ _ (RCanL _)) ].
      apply nd_rule.
      destruct l.
      destruct l0.
      assert (h0=h2). admit.
      subst.
      apply org_fc with (r:=@RLet Γ Δ [] a h1 h h2). 
      auto.
      auto.
      *)
    admit.
    apply (Prelude_error "systemfc cut rule invoked with [a|=[b]] [[b]|=[]]").
    apply (Prelude_error "systemfc cut rule invoked with [a|=[b]] [[b]|=[x,,y]]").
    apply (Prelude_error "systemfc rule invoked with [a|=[]]  [[]|=c]").
    apply (Prelude_error "systemfc rule invoked with [a|=[b,,c]] [[b,,c]|=z]").
    Defined.

  Instance SystemFCa_sequents : @SequentND _ RuleΓΔ _ _ :=
  { snd_cut := SystemFCa_cut }.
    apply Build_SequentND.
    intros.
    induction a.
    destruct a; simpl.
    (*
    apply nd_rule.
      destruct l.
      apply org_fc with (r:=RVar _ _ _ _).
      auto.
    apply nd_rule.
      apply org_fc with (r:=RVoid _ _ ).
      auto.
    eapply nd_comp.
      eapply nd_comp; [ apply nd_llecnac | idtac ].
      apply (nd_prod IHa1 IHa2).
      apply nd_rule.
        apply org_fc with (r:=RJoin _ _ _ _ _ _). 
        auto.
      admit.
      *)
      admit.
      admit.
      admit.
      admit.
      Defined.

  Definition SystemFCa_left a b c : ND RuleΓΔ [(b,c)] [((a,,b),(a,,c))].
    admit.
    (*
    eapply nd_comp; [ apply nd_llecnac | eapply nd_comp; [ idtac | idtac ] ].
    eapply nd_prod; [ apply snd_initial | apply nd_id ].
    apply nd_rule.
    apply org_fc with (r:=RJoin Γ Δ a b a c).
    auto.
    *)
    Defined.

  Definition SystemFCa_right a b c : ND RuleΓΔ [(b,c)] [((b,,a),(c,,a))].
    admit.
    (*
    eapply nd_comp; [ apply nd_rlecnac | eapply nd_comp; [ idtac | idtac ] ].
    eapply nd_prod; [ apply nd_id | apply snd_initial ].
    apply nd_rule.
    apply org_fc with (r:=RJoin Γ Δ b a c a).
    auto.
    *)
    Defined.

  Instance SystemFCa_sequent_join : @ContextND _ _ _ _ SystemFCa_sequents :=
  { cnd_expand_left  := fun a b c => SystemFCa_left  c a b
  ; cnd_expand_right := fun a b c => SystemFCa_right c a b }.
    (*
    intros; apply nd_rule. simpl.
      apply (org_fc _ _ _ _ ((RArrange _ _ _ _ _ (RCossa _ _ _)))).
      auto.

    intros; apply nd_rule. simpl.
      apply (org_fc _ _ _ _ (RArrange _ _ _ _ _ (RAssoc _ _ _))); auto.

    intros; apply nd_rule. simpl.
      apply (org_fc _ _ _ _ (RArrange _ _ _ _ _ (RCanL _))); auto.

    intros; apply nd_rule. simpl.
      apply (org_fc _ _ _ _ (RArrange _ _ _ _ _ (RCanR _))); auto.

    intros; apply nd_rule. simpl.
      apply (org_fc _ _ _ _ (RArrange _ _ _ _ _ (RuCanL _))); auto.

    intros; apply nd_rule. simpl.
      apply (org_fc _ _ _ _ (RArrange _ _ _ _ _ (RuCanR _))); auto.
      *)
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      Defined.

  Instance OrgFC : @ND_Relation _ RuleΓΔ.
    Admitted.

  Instance OrgFC_SequentND_Relation : SequentND_Relation SystemFCa_sequent_join OrgFC.
    admit.
    Defined.

  Definition OrgFC_ContextND_Relation
    : @ContextND_Relation _ _ _ _ _ SystemFCa_sequent_join OrgFC OrgFC_SequentND_Relation.
    admit.
    Defined.

  (* 5.1.2 *)
  Instance SystemFCa : @ProgrammingLanguage (LeveledHaskType Γ ★) _ :=
  { pl_eqv                := OrgFC_ContextND_Relation
  ; pl_snd                := SystemFCa_sequents
  }.

End HaskProgrammingLanguage.
