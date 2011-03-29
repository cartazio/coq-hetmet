(*********************************************************************************************************************************)
(* ReificationsAndGeneralizedArrows:                                                                                             *)
(*                                                                                                                               *)
(*   For each pair of enrichments E1 and E2, there is a bijection between the generalized arrows E1->E2 and the reifications     *)
(*   E1->E2                                                                                                                      *)
(*                                                                                                                               *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
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
Require Import Enrichment_ch2_8.
Require Import RepresentableStructure_ch7_2.
Require Import Reification.
Require Import GeneralizedArrow.
Require Import GeneralizedArrowFromReification.
Require Import ReificationFromGeneralizedArrow.
Require Import ReificationCategory.
Require Import GeneralizedArrowCategory.

Section ReificationsEquivalentToGeneralizedArrows.

  Ltac if_transitive :=
    match goal with [ |- ?A ≃ ?B ] => refine (@if_comp _ _ _ _ _ _ _ A _ _ _ B _ _)
    end.

  Lemma roundtrip_lemma'
    `{C:Category}`{D:Category}`{E:Category}
    {Gobj}(G:Functor E D Gobj) G_full G_faithful {Fobj}(F:Functor C (FullImage G) Fobj) :
    ((F >>>> ff_functor_section_functor G G_full G_faithful) >>>> G) ≃ (F >>>> InclusionFunctor _ _).
    if_transitive.
      apply (if_associativity F (ff_functor_section_functor G _ _) G).
      apply if_respects.
        apply if_id.
        if_transitive; [ idtac | apply if_left_identity ].
    apply (if_comp(F2:=(ff_functor_section_functor G G_full G_faithful) >>>> RestrictToImage G >>>> InclusionFunctor _ _)).
    apply if_inv.
    apply (if_associativity (ff_functor_section_functor G G_full G_faithful) (RestrictToImage G) (InclusionFunctor D (FullImage G))).
    apply if_respects.
    apply ff_functor_section_splits_niso.
    apply if_id.
    Qed.

  Definition roundtrip_lemma
    `(K:SurjectiveEnrichment se) `(C:MonicMonoidalEnrichment e ce) (reification : Reification K C (me_i C))
    := roundtrip_lemma' (HomFunctor C (me_i C)) (ffme_mf_full C) (ffme_mf_faithful C) (step1_functor K C reification).

  Lemma roundtrip_reification_to_reification
    `(K:SurjectiveEnrichment se) `(C:MonicMonoidalEnrichment e ce) (reification : Reification K C (me_i C))
    : reification ≃ reification_from_garrow K C (garrow_from_reification K C reification).
    simpl.
    unfold mon_f.
    unfold garrow_functor.
    apply (if_comp(F2:=(step1_functor K C reification >>>> InclusionFunctor _ (FullImage (HomFunctor C (me_i C)))))).
       apply (@step1_niso _ K _ _ C reification).
       apply (if_inv (roundtrip_lemma K C reification)).
    Qed.

  Lemma roundtrip_garrow_to_garrow
    `(K:SurjectiveEnrichment se) `(C:MonicMonoidalEnrichment e ce) (garrow : GeneralizedArrow K C)
    : garrow ≃ garrow_from_reification K C (reification_from_garrow K C garrow).
    apply (ffc_functor_weakly_monic _ (ffme_mf_full C) (ffme_mf_faithful C) (ffme_mf_conservative C) (ffme_mf_conservative C)).
    apply if_inv.
    apply (if_comp(F2:=(step1_functor K C (reification_from_garrow K C garrow)
           >>>> InclusionFunctor _ (FullImage (HomFunctor C (me_i C)))))).
    unfold mf_f.
    unfold garrow_from_reification.
    unfold garrow_functor.
    unfold step2_functor.
    set (@roundtrip_lemma _ K _ _ C) as q.
    apply (q (reification_from_garrow K C garrow)).
    apply if_inv.
    apply (step1_niso K C (reification_from_garrow K C garrow)).
    Qed.

End ReificationsEquivalentToGeneralizedArrows.
