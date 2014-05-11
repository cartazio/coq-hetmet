(*********************************************************************************************************************************)
(* ProgrammingLanguageFlattening                                                                                                 *)
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
Require Import BinoidalCategories.
Require Import PreMonoidalCategories.
Require Import MonoidalCategories_ch7_8.
Require Import Coherence_ch7_8.
Require Import Enrichment_ch2_8.
Require Import RepresentableStructure_ch7_2.
Require Import FunctorCategories_ch7_7.

Require Import Reification.
Require Import NaturalDeduction.
Require Import NaturalDeductionCategory.
Require Import GeneralizedArrow.
Require Import ProgrammingLanguage.
Require Import ProgrammingLanguageReification.
Require Import SectionRetract_ch2_4.
Require Import GeneralizedArrowFromReification.
Require Import Enrichments.
Require Import ReificationsAndGeneralizedArrows.

Section Flattening.

  Context `(Guest:ProgrammingLanguage) `(Host :ProgrammingLanguage).
  Context (GuestHost:TwoLevelLanguage Guest Host).

  Definition FlatObject (x:TypesL Host) :=
    forall y1 y2, not ((reification_r_obj GuestHost y1 y2)=x).

  Instance FlatSubCategory : FullSubcategory (TypesL Host) FlatObject.

    Context  (F:RetractionOfCategories (TypesL Host) (FullSubCategoriesAreCategories FlatSubCategory)).

    Definition FlatteningOfReification HostMonic HostMonoidal :=
      (ga_functor
        (@garrow_from_reification
          (TypesEnrichedInJudgments Guest)
          (TypesEnrichedInJudgments Host)
          HostMonic HostMonoidal GuestHost))
        >>>> F.

    Lemma FlatteningIsNotDestructive HostMonic HostMonoidal : 
      FlatteningOfReification HostMonic HostMonoidal >>>> retraction_retraction F >>>> HomFunctor _ []
      ≃ (reification_rstar GuestHost).
      apply if_inv.
      set (@roundtrip_reification_to_reification (TypesEnrichedInJudgments Guest) (TypesEnrichedInJudgments Host)
        HostMonic HostMonoidal GuestHost) as q.
      unfold mf_F in *; simpl in *.
      eapply if_comp.
      apply q.
      clear q.
      unfold mf_F; simpl.
      unfold pmon_I.
      apply (if_respects
        (garrow_functor (TypesEnrichedInJudgments Guest) HostMonic HostMonoidal GuestHost)
        (FlatteningOfReification HostMonic HostMonoidal >>>> retraction_retraction F)
        (HomFunctor (TypesL Host) [])
        (HomFunctor (TypesL Host) [])); [ idtac | apply (if_id _) ].
      unfold FlatteningOfReification.
      unfold mf_F; simpl.
      apply if_inv.
      eapply if_comp.
      apply (if_associativity (garrow_functor (TypesEnrichedInJudgments Guest) HostMonic HostMonoidal GuestHost) F
               (retraction_retraction F)).
      eapply if_comp; [ idtac | apply if_right_identity ].
      apply (if_respects
        (garrow_functor (TypesEnrichedInJudgments Guest) HostMonic HostMonoidal GuestHost)
        (garrow_functor (TypesEnrichedInJudgments Guest) HostMonic HostMonoidal GuestHost)
        (F >>>> retraction_retraction F)
        (functor_id _)).
      apply (if_id _).
      apply retraction_composes.
      Qed.

End Flattening.


