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
Require Import MonoidalCategories_ch7_8.
Require Import Coherence_ch7_8.
Require Import Enrichment_ch2_8.
Require Import RepresentableStructure_ch7_2.
Require Import FunctorCategories_ch7_7.

Require Import Reification.
Require Import NaturalDeduction.
Require Import NaturalDeductionCategory.
Require Import GeneralizedArrow.
Require Import GeneralizedArrowFromReification.
Require Import ProgrammingLanguage.
Require Import ProgrammingLanguageReification.
Require Import ReificationsAndGeneralizedArrows.

Section Flattening.

  Context (Guest:ProgrammingLanguageSMME) (Host :ProgrammingLanguageSMME).
  Context (GuestHost:TwoLevelLanguage Guest Host).

  Definition FlatObject (x:TypesL _ _ Host) :=
    forall y1 y2, not ((reification_r_obj GuestHost y1 y2)=x).

  Definition FlatSubCategory := FullSubcategory (TypesL _ _ Host) FlatObject.

    Context  (F:Retraction (TypesL _ _ Host) FlatSubCategory).

    Definition FlatteningOfReification :=
      garrow_from_reification Guest Host GuestHost >>>> F.

(*
    Lemma FlatteningIsNotDestructive : 
      FlatteningOfReification >>>> retraction_retraction F >>>> HomFunctor _ (me_i Host) ≃ GuestHost.
      apply if_inv.
      set (@roundtrip_reification_to_reification _ Guest _ _ Host GuestHost) as q.
      unfold mf_f in *; simpl in *.
      apply (if_comp q).
      clear q.
      unfold me_mf; simpl.
      unfold mf_f; simpl.
      refine (if_respects _ (if_id _)).
      unfold FlatteningOfReification.
      unfold mf_f; simpl.
      eapply if_comp.
      Focus 2.
      eapply if_inv.
      apply (if_associativity (garrow_functor Guest Host GuestHost) F (retraction_retraction F)).
      eapply if_comp.
      eapply if_inv.
      apply if_right_identity.
      refine (if_respects (if_id _) _).
      apply if_inv.
      apply retraction_composes.
      Qed.
*)
End Flattening.


