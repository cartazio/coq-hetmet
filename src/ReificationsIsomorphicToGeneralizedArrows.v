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

    Definition M1 {c1 c2 : SmallSMMEs.SMMEs} :
      (c1 ~~{ MorphismsOfCategoryOfGeneralizedArrows }~~> c2) ->
      (c1 ~~{ MorphismsOfCategoryOfReifications }~~> c2).
      intro GA.
      destruct GA; [ apply roi_id | idtac ].
      apply roi_reif.
      apply reification_from_garrow.
      apply g.
      Defined.

    Lemma invert_ga : forall (a: SMME)
      (f:a~~{MorphismsOfCategoryOfGeneralizedArrows}~~>a),
      (f = gaoi_id _) \/ (exists f', f = gaoi_ga _ _ f').
      admit.
      Qed.

    Lemma invert_reif : forall (a: SMME)
      (f:a~~{MorphismsOfCategoryOfReifications}~~>a),
      (f = roi_id _) \/ (exists f', f = roi_reif _ _ f').
      admit.
      Qed.

    Definition M1_Functor : Functor MorphismsOfCategoryOfGeneralizedArrows MorphismsOfCategoryOfReifications (fun x => x).
      refine {| fmor := fun a b f => M1 f |}.
      intros.
        unfold hom in *.
        unfold eqv in *.
        simpl in *.
        destruct f.
        set (invert_ga _ f') as q.
        destruct q; subst.
        apply if_id.
        simpl in *.
        destruct H0; subst.
        apply H.
        simpl in *.
        destruct f'; simpl in *.
        apply H.
        apply H.
      intros; simpl.
        apply if_id.
      intros.
        simpl.
        destruct f; simpl.
        apply if_id.
        destruct g; simpl.
        apply if_id.
        unfold mf_f; simpl.
        apply (if_associativity 
          ((ga_functor g0 >>>> RepresentableFunctor s0 (mon_i s0))) (ga_functor g) (RepresentableFunctor s2 (me_i s2))).
        Defined.

    Definition M2 (c1 c2 : SmallSMMEs.SMMEs) :
      (c1 ~~{ MorphismsOfCategoryOfReifications }~~> c2) ->
      (c1 ~~{ MorphismsOfCategoryOfGeneralizedArrows }~~> c2).
      intro RE.
      destruct RE; [ apply gaoi_id | idtac ].
      apply gaoi_ga.
      apply (garrow_from_reification s1 s2 r).
      Defined.

    Lemma M2_respects :
      forall a b (f f':a~~{MorphismsOfCategoryOfReifications}~~>b),
         f ~~ f' ->
         M2 a b f ~~ M2 a b f'.
      intros.
        unfold hom in *.
        unfold eqv in *.
        simpl in *.
        destruct f.
        set (invert_reif _ f') as q.
        destruct q; subst.
        apply if_id.
        simpl in *.
        destruct H0; subst.
        simpl in *.
        unfold garrow_functor.
        unfold step2_functor.
        apply (if_comp H).
        clear H.
        apply (if_comp (@step1_niso _ smme _ _ smme x)).
        apply if_inv.
        apply (@roundtrip_lemma _ smme _ _ smme x).
      simpl in *.
        destruct f'; simpl in *.
        apply if_inv.
        apply if_inv in H.
        apply (if_comp H).
        clear H.
        unfold garrow_functor.
        unfold step2_functor.
        apply (if_comp (@step1_niso _ smme _ _ smme r)).
        apply if_inv.
        apply (@roundtrip_lemma _ smme _ _ smme r).
      simpl in *.
        unfold garrow_functor.
        unfold step2_functor.
        apply if_inv in H.
        set (if_comp H (@step1_niso _ s1 _ _ s2 r)) as yy.
        set (if_comp (if_inv (@step1_niso _ s1 _ _ s2 r0)) yy) as yy'.
        apply (if_comp (@roundtrip_lemma _ s1 _ _ s2 r)).
        apply if_inv.
        apply (if_comp (@roundtrip_lemma _ s1 _ _ s2 r0)).
        apply yy'.
        Qed.

    Definition M2_Functor : Functor MorphismsOfCategoryOfReifications MorphismsOfCategoryOfGeneralizedArrows (fun x => x).
      refine {| fmor := fun a b f => M2 _ _ f |}.
      apply M2_respects.
      intros; simpl; apply if_id.
      intros.
        simpl.
        destruct f; simpl.
        apply if_id.
        destruct g; simpl.
        apply if_id.
        unfold mf_f; simpl.
        apply (if_respects
          (F0:=((garrow_functor s1 s0 r >>>> RepresentableFunctor s0 (mon_i s0)) >>>> garrow_functor s0 s2 r0))
          (F1:=(garrow_functor s1 s2 (compose_reifications s1 s0 s2 r r0)))
          (G0:=(RepresentableFunctor s2 (mon_i s2)))
          (G1:=(RepresentableFunctor s2 (mon_i s2))));
        [ idtac | apply if_id ].
        admit.
        Defined.

    Theorem ReificationsAreGArrows : IsomorphicCategories CategoryOfGeneralizedArrows CategoryOfReifications.
      refine {| ic_f := M1_Functor ; ic_g := M2_Functor |}.
      unfold EqualFunctors; intros; apply heq_morphisms_intro; unfold eqv in *; simpl in *.
        unfold hom in *.
        set (@roundtrip_garrow_to_garrow _ a _ _ b) as q.
        destruct f; simpl in *.
        apply H.
        apply if_inv.
        apply (if_comp (if_inv H)).
        clear H.
        unfold mf_f in q.
        apply (if_respects(F0:=ga_functor g)(F1:=garrow_functor s1 s2 (reification_from_garrow s1 s2 g))
          (G0:=RepresentableFunctor s2 (mon_i s2))(G1:=RepresentableFunctor s2 (mon_i s2))).
        apply q.
        apply if_id.
        
      unfold EqualFunctors; intros; apply heq_morphisms_intro; unfold eqv in *; simpl in *.
        unfold hom in *.
        set (@roundtrip_reification_to_reification _ a _ _ b) as q.
        destruct f; simpl.
        apply H.
        apply if_inv.
        apply (if_comp (if_inv H)).
        clear H.
        simpl.
        unfold mf_f; simpl.
        simpl in q.
        unfold mf_f in q.
        simpl in q.
        apply q.
        Qed.

End ReificationsIsomorphicToGeneralizedArrows.
