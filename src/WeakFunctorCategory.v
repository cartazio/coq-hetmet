(*********************************************************************************************************************************)
(* WeakFunctorCategory:                                                                                                          *)
(*                                                                                                                               *)
(*   A category whose morphisms are functors, identified up to natural isomorphism (not equality).  This pulls most of the       *)
(*   heavy lifting out of ReificationsEquivalentToGeneralizedArrows, since the definitions in that context cause Coq to bog      *)
(*   down and run unbearably slowly                                                                                              *)
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
(*Require Import Enrichment_ch2_8.*)
(*Require Import RepresentableStructure_ch7_2.*)

Section WeakFunctorCategory.

  (* We can't handle categories directly due to size issues.
   * Therefore, we ask the user to supply two types "Cat" and "Mor"
   * which index the "small categories"; we then construct a large
   * category relative to those. *)
  Structure SmallCategories :=
  { small_cat       : Type
  ; small_ob        : small_cat -> Type
  ; small_hom       : forall c:small_cat, small_ob c -> small_ob c -> Type
  ; small_cat_cat   : forall c:small_cat, Category (small_ob c) (small_hom c)
  }.

  Context {sc:SmallCategories}.
  Structure SmallFunctors :=
  { small_func       : small_cat sc -> small_cat sc -> Type
  ; small_func_fobj  : forall {c1}{c2}, small_func c1 c2 -> (small_ob sc c1 -> small_ob sc c2)
  ; small_func_func  : forall {c1}{c2}(f:small_func c1 c2), Functor (small_cat_cat sc c1) (small_cat_cat sc c2) (small_func_fobj f)

  (* proof that our chosen indexing contains identity functors and is closed under composition *)
  ; small_func_id    : forall  c1 , small_func c1 c1
  ; small_func_id_id : forall {c1}, small_func_func (small_func_id c1) ≃ functor_id (small_cat_cat sc c1)
  ; small_func_comp  : forall {c1}{c2}{c3}, small_func c1 c2 -> small_func c2 c3 -> small_func c1 c3
  ; small_func_comp_comp : forall {c1}{c2}{c3}(f:small_func c1 c2)(g:small_func c2 c3), 
    small_func_func (small_func_comp f g) ≃ small_func_func f >>>> small_func_func g
  }.

  Instance WeakFunctorCategory `(sf:SmallFunctors) : Category (small_cat sc) (small_func sf) :=
  { id   := fun a         => small_func_id sf a
  ; comp := fun a b c f g => small_func_comp sf f g
  ; eqv  := fun a b f g   => small_func_func sf f ≃ small_func_func sf g
  }.
    intros; simpl.
    apply Build_Equivalence.
      unfold Reflexive; simpl; intros; apply if_id.
      unfold Symmetric; simpl; intros; apply if_inv; auto.
      unfold Transitive; simpl; intros; eapply if_comp. apply H. apply H0.
    intros; simpl.
      unfold Proper; unfold respectful; simpl; intros.
      eapply if_comp.
      apply small_func_comp_comp.
      eapply if_inv.
      eapply if_comp.
      apply small_func_comp_comp.
      eapply if_respects. apply if_inv. apply H. apply if_inv. apply H0.
    intros; simpl.
      eapply if_comp.
      apply small_func_comp_comp.
      eapply if_comp; [ idtac | apply if_left_identity ].
      eapply if_respects; try apply if_id.
      apply small_func_id_id.
    intros; simpl.
      eapply if_comp.
      apply small_func_comp_comp.
      eapply if_comp; [ idtac | apply if_right_identity ].
      eapply if_respects; try apply if_id.
      apply small_func_id_id.
    intros; simpl.
      eapply if_comp.
      eapply if_comp ; [ idtac | apply small_func_comp_comp ].
      apply if_id.
      apply if_inv.
      eapply if_comp.
      eapply if_comp ; [ idtac | apply small_func_comp_comp ].
      apply if_id.
      eapply if_comp.
      eapply if_respects.
      eapply if_id.
      eapply small_func_comp_comp.
      apply if_inv.
      eapply if_comp.
      eapply if_respects.
      eapply small_func_comp_comp.
      eapply if_id.
      set (@if_associativity) as q.
      apply (q _ _ _ _ _ _ _ _ _ _ _ _ _ (small_func_func sf f) _ (small_func_func sf g) _ (small_func_func sf h)).
      Defined.
End WeakFunctorCategory.
Coercion WeakFunctorCategory : SmallFunctors >-> Category.
Coercion small_func_func : small_func >-> Functor.
Coercion small_cat_cat : small_cat >-> Category.
Coercion small_cat : SmallCategories >-> Sortclass.

(*
Add Parametric Relation (Ob:Type)(Hom:Ob->Ob->Type)(C:Category Ob Hom)(a b:Ob) : (hom a b) (eqv a b)
  reflexivity proved by  (@Equivalence_Reflexive  _ _ (eqv_equivalence a b))
  symmetry proved by     (@Equivalence_Symmetric  _ _ (eqv_equivalence a b))
  transitivity proved by (@Equivalence_Transitive _ _ (eqv_equivalence a b))
  as parametric_relation_eqv.
  Add Parametric Morphism `(c:Category Ob Hom)(a b c:Ob) : (comp a b c)
  with signature (eqv _ _ ==> eqv _ _ ==> eqv _ _) as parametric_morphism_comp.
  auto.
  Defined.*)

Section WeakFunctorCategoryIsomorphism.
  (* Here we sort of set up exactly the conditions needed to trigger
   * the ReificationsAreGeneralizedArrows proof; again, I'm doing it here
   * because the instant I import Reification or GeneralizedArrow, Coq
   * becomes nearly unusable.  *)

  (* same objects (SMME's) for both categories, and the functor is IIO *)
  Context {SMMEs:SmallCategories}.
  Context {GA:@SmallFunctors SMMEs}.
  Context {RE:@SmallFunctors SMMEs}.

  Context (M1:forall c1 c2, (c1~~{GA}~~>c2) -> (c1~~{RE}~~>c2)).
  Context (M2:forall c1 c2, (c1~~{RE}~~>c2) -> (c1~~{GA}~~>c2)).
  Implicit Arguments M1 [[c1][c2]].
  Implicit Arguments M2 [[c1][c2]].

  Section GeneralCase.
    Context (m1_respects_eqv
      : forall (c1 c2:SMMEs) (f:c1~~{GA}~~>c2) (g:c1~~{GA}~~>c2),
               (small_func_func _ f) ≃ (small_func_func _ g) -> small_func_func RE (M1 f) ≃ small_func_func RE (M1 g)).
    Context (m2_respects_eqv
      : forall (c1 c2:SMMEs) (f:c1~~{RE}~~>c2) (g:c1~~{RE}~~>c2),
               (small_func_func _ f) ≃ (small_func_func _ g) -> small_func_func GA (M2 f) ≃ small_func_func GA (M2 g)).
    Context (m1_preserves_id
      : forall c1, small_func_func _ (M1 (small_func_id GA c1)) ≃ small_func_id RE c1).
    Context (m2_preserves_id
      : forall c1, small_func_func _ (M2 (small_func_id RE c1)) ≃ small_func_id GA c1).
    Context (m1_respects_comp :
      forall (c1 c2 c3:SMMEs) (f:c1~~{GA}~~>c2) (g:c2~~{GA}~~>c3),
        small_func_func _ (small_func_comp _ (M1 f) (M1 g)) ≃ 
        small_func_func _ ((M1 (small_func_comp _ f g)))).
    Context (m2_respects_comp :
      forall (c1 c2 c3:SMMEs) (f:c1~~{RE}~~>c2) (g:c2~~{RE}~~>c3),
        small_func_func _ (small_func_comp _ (M2 f) (M2 g)) ≃ 
        small_func_func _ ((M2 (small_func_comp _ f g)))).
    Context (m1_m2_id
      : forall (c1 c2:SMMEs) (f:c1~~{GA}~~>c2),
        small_func_func _ (M2 (M1 f)) ≃ small_func_func _ f).
    Context (m2_m1_id
      : forall (c1 c2:SMMEs) (f:c1~~{RE}~~>c2),
        small_func_func _ (M1 (M2 f)) ≃ small_func_func _ f).

    Definition F1 : Functor GA RE (fun x => x).
      refine  {| fmor := fun a b f => M1 f |}.
      intros. 
        unfold eqv; simpl.
        apply m1_respects_eqv.
        apply H.
      intros.
        unfold eqv; simpl; intros.
        apply m1_preserves_id. 
      intros. 
        unfold eqv; simpl.
        set m1_respects_comp as q.
        unfold eqv in q.
        apply q.
        Defined.

    Definition F2 : Functor RE GA (fun x => x).
      refine  {| fmor := fun a b f => M2 f |}.
      intros. 
        unfold eqv; simpl.
        apply m2_respects_eqv.
        apply H.
      intros.
        unfold eqv; simpl; intros.
        apply m2_preserves_id. 
      intros. 
        unfold eqv; simpl.
        set m2_respects_comp as q.
        unfold eqv in q.
        apply q.
        Defined.

    Theorem WeakFunctorCategoriesIsomorphic : IsomorphicCategories GA RE.
      refine {| ic_f := F1 ; ic_g := F2 |}.
      unfold EqualFunctors; intros; apply heq_morphisms_intro; unfold eqv in *; simpl in *.
        eapply if_comp.
        apply m1_m2_id.
        apply H.
      unfold EqualFunctors; intros; apply heq_morphisms_intro; unfold eqv in *; simpl in *.
        eapply if_comp.
        apply m2_m1_id.
        apply H.
        Qed.

  End GeneralCase.
(*
  (* now, the special case we can really use: M1 and M2 each consist of post-composition *)
  Section WeakFunctorCategoryPostCompositionIsomorphism.

    Context (M1_postcompose_obj : forall c1:SMMEs, c1 -> c1).
    Context (M1_postcompose     : forall c1:SMMEs, Functor c1 c1 (M1_postcompose_obj c1)).

    Context (M2_postcompose_obj : forall c1:SMMEs, c1 -> c1).
    Context (M2_postcompose     : forall c1:SMMEs, Functor c1 c1 (M1_postcompose_obj c1)).

    Context (M1_M2_id           : forall c1:SMMEs, M1_postcompose c1 >>>> M2_postcompose c1 ≃ functor_id _).
    Context (M2_M1_id           : forall c1:SMMEs, M2_postcompose c1 >>>> M1_postcompose c1 ≃ functor_id _).

    Context (M1_postcompose_act : forall (c1 c2:SMMEs)(f:c1~~{GA}~~>c2),
      small_func_func _ (M1 f) ≃ small_func_func _ f >>>> M1_postcompose c2).
    Context (M2_postcompose_act : forall (c1 c2:SMMEs)(f:c1~~{RE}~~>c2),
      small_func_func _ (M2 f) ≃ small_func_func _ f >>>> M2_postcompose c2).

    Definition F1' : Functor GA RE (fun x => x).
      apply F1; intros; simpl.
        eapply if_comp.
        apply M1_postcompose_act.
        apply if_inv.
        eapply if_comp.
        apply M1_postcompose_act.
        apply if_respects; try apply if_id.
        apply if_inv; auto.
      apply (if_comp (M1_postcompose_act _ _ _)).
        apply M1_postcompose_act.
      
      
    Theorem WeakFunctorCategoryPostCompositionIsomorphism : IsomorphicCategories GA RE F1 F2
    End WeakFunctorCategoryPostCompositionIsomorphism.
    *)
End WeakFunctorCategoryIsomorphism.


