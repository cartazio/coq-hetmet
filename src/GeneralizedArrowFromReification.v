(*********************************************************************************************************************************)
(* GeneralizedArrowFromReification:                                                                                              *)
(*                                                                                                                               *)
(*   Turn a generalized arrow into a reification                                                                                 *)
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

Section GArrowFromReification.

  Context  `(K:SurjectiveEnrichment ke) `(C:MonicMonoidalEnrichment ce cme) (reification : Reification K C (me_i C)).

  Fixpoint garrow_fobj_ vk : C :=
    match vk with
    | T_Leaf None     => me_i C
    | T_Leaf (Some a) => match a with (a1,a2) => reification_r reification a1 a2 end
    | t1,,t2          => me_f C (pair_obj (garrow_fobj_ t1) (garrow_fobj_ t2))
    end.

  Definition garrow_fobj vk := garrow_fobj_ (projT1 (se_decomp _ K vk)).

  Definition homset_tensor_iso
    : forall vk:enr_v_mon K, (reification_rstar reification vk) ≅ ehom(ECategory:=C) (me_i C) (garrow_fobj vk).
    intros.
    unfold garrow_fobj.
    set (se_decomp _ K  vk) as sevk.
    destruct sevk.
    simpl in *.
    rewrite e.
    clear e.
    induction x; simpl.

    destruct a.
      destruct p.

      apply iso_inv.
        apply (ni_iso (reification_commutes reification e) e0).

      eapply id_comp.
        apply iso_inv.
        apply (mf_id (reification_rstar reification)).
        apply (mf_id (me_mf C)).

      eapply id_comp.
        apply iso_inv.
          apply (ni_iso (mf_coherence (reification_rstar reification)) (pair_obj _ _)).
        eapply id_comp.
          Focus 2.
          apply (ni_iso (mf_coherence (me_mf C)) (pair_obj _ _)).
          unfold bin_obj.
          apply (functors_preserve_isos (enr_v_f C) (a:=(pair_obj _ _))(b:=(pair_obj _ _))).
          apply (iso_prod IHx1 IHx2).
        Defined.

  Definition garrow_fobj' (vk:enr_v_mon K) : FullImage (RepresentableFunctor C (me_i C)).
    exists (ehom(ECategory:=C) (me_i C) (garrow_fobj vk)).
    abstract (exists (garrow_fobj vk); auto).
    Defined.

  Definition step1_mor {a b}(f:a~~{enr_v_mon K}~~>b) : (garrow_fobj' a)~~{FullImage (RepresentableFunctor C (me_i C))}~~>(garrow_fobj' b).
    exists (iso_backward (homset_tensor_iso a) 
        >>> reification_rstar reification \ f
        >>> iso_forward (homset_tensor_iso  b)).
    abstract (auto).
    Defined.

  Definition step1_functor : Functor (enr_v_mon K) (FullImage (RepresentableFunctor C (me_i C))) garrow_fobj'.
    refine {| fmor := fun a b f => step1_mor f |}.
    abstract (intros; unfold step1_mor; simpl;
              apply comp_respects; try reflexivity;
              apply comp_respects; try reflexivity;
              apply fmor_respects; auto).
    abstract (intros; unfold step1_mor; simpl;
      setoid_rewrite fmor_preserves_id;
      setoid_rewrite right_identity;
      apply iso_comp2).
    abstract (intros;
      unfold step1_mor;
      simpl;
      repeat setoid_rewrite <- associativity;
      apply comp_respects; try reflexivity;
      repeat setoid_rewrite associativity;
      apply comp_respects; try reflexivity;
      setoid_rewrite juggle2;
      set (iso_comp1 (homset_tensor_iso b)) as qqq;
      setoid_rewrite qqq;
      clear qqq;
      setoid_rewrite right_identity;
      apply (fmor_preserves_comp reification)).
      Defined.

  Definition step1_niso : reification ≃ step1_functor >>>> InclusionFunctor _ (FullImage (RepresentableFunctor C (me_i C))).
    exists (fun c1 => homset_tensor_iso c1).
    abstract (intros;
              simpl;
              repeat setoid_rewrite <- associativity;
              setoid_rewrite iso_comp1;
              setoid_rewrite left_identity;
              reflexivity).
    Qed.
    Opaque homset_tensor_iso.

  Definition step2_functor := ff_functor_section_functor _ (ffme_mf_full C) (ffme_mf_faithful C).

  Definition garrow_functor := step1_functor >>>> step2_functor.

  Lemma garrow_functor_monoidal_niso
    : (garrow_functor **** garrow_functor) >>>> (mon_f C) <~~~> (mon_f (enr_v_mon K)) >>>> garrow_functor.
    unfold garrow_functor.
    admit.
    Defined.
  Lemma garrow_functor_monoidal_iso
    : mon_i C ≅ garrow_functor (mon_i (enr_v_mon K)).
    admit.
    Defined.

  Instance garrow_functor_monoidal : MonoidalFunctor (enr_v_mon K) C garrow_functor :=
    { mf_coherence := garrow_functor_monoidal_niso
    ; mf_id        := garrow_functor_monoidal_iso
    }.
    admit.
    admit.
    admit.
    Defined.

  Definition garrow_from_reification : GeneralizedArrow K C.
    refine
      {| ga_functor          := garrow_functor
       ; ga_functor_monoidal := garrow_functor_monoidal
      |}.
    Defined.

End GArrowFromReification.
Opaque homset_tensor_iso.
