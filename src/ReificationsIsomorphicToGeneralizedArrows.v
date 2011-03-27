(*********************************************************************************************************************************)
(* ReificationsEquivalentToGeneralizedArrows:                                                                                    *)
(*                                                                                                                               *)
(*   The category of generalized arrows and the category of reifications are equivalent categories.                              *)
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
Require Import ReificationsEquivalentToGeneralizedArrows.
Require Import WeakFunctorCategory.


Section ReificationsIsomorphicToGeneralizedArrows.

    Definition M1 (c1 c2 : SmallSMMEs.SMMEs) :
      (c1 ~~{ MorphismsOfCategoryOfGeneralizedArrows }~~> c2) ->
      (c1 ~~{ MorphismsOfCategoryOfReifications }~~> c2).
      intro GA.
      destruct GA; [ apply roi_id | idtac ].
      apply roi_reif.
      apply reification_from_garrow.
      apply g.
      Defined.

    Definition M2 (c1 c2 : SmallSMMEs.SMMEs) :
      (c1 ~~{ MorphismsOfCategoryOfReifications }~~> c2) ->
      (c1 ~~{ MorphismsOfCategoryOfGeneralizedArrows }~~> c2).
      intro RE.
      destruct RE; [ apply gaoi_id | idtac ].
      apply gaoi_ga.
      apply (garrow_from_reification s1 s2 r).
      Defined.

    (*

     * Oh my, this is massively embarrassing.  In the paper I claim
     * that Generalized Arrows form a category and Reifications form a
     * category, when in fact they form merely a SEMIcategory (see
     * http://ncatlab.org/nlab/show/semicategory) since we cannot be sure that the identity functor on the

    Theorem ReificationsAreGArrows : IsomorphicCategories CategoryOfGeneralizedArrows CategoryOfReifications.
      apply WeakFunctorCategoriesIsomorphic with (M1:=M1) (M2:=M2).
      destruct g.
      intros.
      simpl.
      simpl in H.
      split f.
      destruct f.
      dependent destruction f.
      intros until g.
      destruct f.
      simpl.
      inversion g.
      destruct f as [ ] _eqn.
      destruct g as [ ] _eqn.
      destruct g.
      subst.
      simpl.
      case g.
      simpl.
      inversion g; subst; intros.
      destruct g.
      Qed.

End ReificationsIsomorphicToGeneralizedArrows.
