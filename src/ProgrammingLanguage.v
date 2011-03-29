(*********************************************************************************************************************************)
(* ProgrammingLanguage                                                                                                           *)
(*                                                                                                                               *)
(*   Basic assumptions about programming languages.                                                                              *)
(*                                                                                                                               *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Categories_ch1_3.
Require Import InitialTerminal_ch2_2.
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
Require Import Enrichment_ch2_8.
Require Import RepresentableStructure_ch7_2.
Require Import FunctorCategories_ch7_7.

Require Import NaturalDeduction.
Require Import NaturalDeductionCategory.

Section Programming_Language.

  Context {T    : Type}.               (* types of the language *)

  Context (Judg : Type).
  Context (sequent : Tree ??T -> Tree ??T -> Judg).
     Notation "cs |= ss" := (sequent cs ss) : pl_scope.

  Context {Rule : Tree ??Judg -> Tree ??Judg -> Type}.

  Notation "H /⋯⋯/ C" := (ND Rule H C) : pl_scope.

  Open Scope pf_scope.
  Open Scope nd_scope.
  Open Scope pl_scope.

  Class ProgrammingLanguage :=
  { pl_eqv                :  @ND_Relation Judg Rule where "pf1 === pf2" := (@ndr_eqv _ _ pl_eqv _ _ pf1 pf2)
  ; pl_tsr                :> @TreeStructuralRules Judg Rule T sequent
  ; pl_sc                 :> @SequentCalculus Judg Rule _ sequent
  ; pl_subst              :> @CutRule Judg Rule _ sequent pl_eqv pl_sc
  ; pl_sequent_join       :> @SequentExpansion Judg Rule T sequent pl_eqv pl_sc pl_subst
  }.
  Notation "pf1 === pf2" := (@ndr_eqv _ _ pl_eqv _ _ pf1 pf2) : temporary_scope3.

  Section LanguageCategory.

    Context (PL:ProgrammingLanguage).

    (* category of judgments in a fixed type/coercion context *)
    Definition Judgments_cartesian := @Judgments_Category_CartesianCat _ Rule pl_eqv.

    Definition JudgmentsL          := Judgments_cartesian.

    Definition identityProof t : [] ~~{JudgmentsL}~~> [t |= t].
      unfold hom; simpl.
      apply nd_seq_reflexive.
      Defined.

    Definition cutProof a b c : [a |= b],,[b |= c] ~~{JudgmentsL}~~> [a |= c].
      unfold hom; simpl.
      apply pl_subst.
      Defined.

    Definition TypesL : ECategory JudgmentsL (Tree ??T) (fun x y => [x|=y]).
      refine
      {| eid   := identityProof
       ; ecomp := cutProof
      |}; intros.
      apply MonoidalCat_all_central.
      apply MonoidalCat_all_central.
      unfold identityProof; unfold cutProof; simpl.
      apply nd_cut_left_identity.
      unfold identityProof; unfold cutProof; simpl.
      apply nd_cut_right_identity.
      unfold identityProof; unfold cutProof; simpl.
      symmetry.
      apply nd_cut_associativity.
      Defined.

    Definition Types_first c : EFunctor TypesL TypesL (fun x => x,,c ).
      refine {| efunc := fun x y => (@se_expand_right _ _ _ _ _ _ _ (@pl_sequent_join PL) c x y) |}.
      intros; apply MonoidalCat_all_central.
      intros. unfold ehom. unfold hom. unfold identityProof. unfold eid. simpl. unfold identityProof.
      apply se_reflexive_right.
      intros. unfold ehom. unfold comp. simpl. unfold cutProof.
      rewrite <- (@ndr_prod_preserves_comp _ _ pl_eqv _ _ (se_expand_right _ c) _ _ (nd_id1 (b|=c0))
                  _ (nd_id1 (a,,c |= b,,c))  _ (se_expand_right _ c)).
      setoid_rewrite (@ndr_comp_right_identity _ _ pl_eqv _ [a,, c |= b,, c]).
      setoid_rewrite (@ndr_comp_left_identity  _ _ pl_eqv [b |= c0]).
      apply se_cut_right.
      Defined.

    Definition Types_second c : EFunctor TypesL TypesL (fun x => c,,x).
      eapply Build_EFunctor.
      instantiate (1:=(fun x y => ((@se_expand_left _ _ _ _ _ _ _ (@pl_sequent_join PL) c x y)))).
      intros; apply MonoidalCat_all_central.
      intros. unfold ehom. unfold hom. unfold identityProof. unfold eid. simpl. unfold identityProof.
      apply se_reflexive_left.
      intros. unfold ehom. unfold comp. simpl. unfold cutProof.
      rewrite <- (@ndr_prod_preserves_comp _ _ pl_eqv _ _ (se_expand_left _ c) _ _ (nd_id1 (b|=c0))
                  _ (nd_id1 (c,,a |= c,,b))  _ (se_expand_left _ c)).
      setoid_rewrite (@ndr_comp_right_identity _ _ pl_eqv _ [c,,a |= c,,b]).
      setoid_rewrite (@ndr_comp_left_identity  _ _ pl_eqv [b |= c0]).
      apply se_cut_left.
      Defined.

    Definition Types_binoidal : BinoidalCat TypesL (@T_Branch _).
      refine
        {| bin_first  := Types_first
         ; bin_second := Types_second
         |}.
      Defined.

    Definition Types_assoc a b : Types_second a >>>> Types_first b <~~~> Types_first b >>>> Types_second a.
      admit.
      Defined.

    Definition Types_cancelr   : Types_first [] <~~~> functor_id _.
      admit.
      Defined.

    Definition Types_cancell   : Types_second [] <~~~> functor_id _.
      admit.
      Defined.

    Definition Types_assoc_ll a b : Types_second (a,,b) <~~~> Types_second b >>>> Types_second a.
      admit.
      Defined.

    Definition Types_assoc_rr a b : Types_first (a,,b) <~~~> Types_first a >>>> Types_first b.
      admit.
      Defined.

    Instance Types_PreMonoidal : PreMonoidalCat Types_binoidal [] :=
        { pmon_assoc    := Types_assoc
        ; pmon_cancell  := Types_cancell
        ; pmon_cancelr  := Types_cancelr
        ; pmon_assoc_rr := Types_assoc_rr
        ; pmon_assoc_ll := Types_assoc_ll
        }.
        admit. (* pentagon law *)
        admit. (* triangle law *)
        admit. (* assoc_rr/assoc coherence *)
        admit. (* assoc_ll/assoc coherence *)
        Defined.

    Definition TypesEnrichedInJudgments : Enrichment.
      refine {| enr_c := TypesL |}.
      Defined.

    Structure HasProductTypes :=
    {
    }.

    Lemma CartesianEnrMonoidal (e:Enrichment) `(C:CartesianCat(Ob:= _)(Hom:= _)(C:=Underlying (enr_c e))) : MonoidalEnrichment e.
      admit.
      Defined.

    (* need to prove that if we have cartesian tuples we have cartesian contexts *)
    Definition LanguagesWithProductsAreSMME : HasProductTypes -> SurjectiveMonicMonoidalEnrichment TypesEnrichedInJudgments.
      admit.
      Defined.

  End LanguageCategory.

End Programming_Language.

Structure ProgrammingLanguageSMME :=
{ plsmme_t       : Type
; plsmme_judg    : Type
; plsmme_sequent : Tree ??plsmme_t -> Tree ??plsmme_t -> plsmme_judg
; plsmme_rule    : Tree ??plsmme_judg -> Tree ??plsmme_judg -> Type
; plsmme_pl      : @ProgrammingLanguage plsmme_t plsmme_judg plsmme_sequent plsmme_rule
; plsmme_smme    : SurjectiveMonicMonoidalEnrichment (TypesEnrichedInJudgments _ _ plsmme_pl)
}.
Coercion plsmme_pl   : ProgrammingLanguageSMME >-> ProgrammingLanguage.
Coercion plsmme_smme : ProgrammingLanguageSMME >-> SurjectiveMonicMonoidalEnrichment.
 
Implicit Arguments ND [ Judgment ].
