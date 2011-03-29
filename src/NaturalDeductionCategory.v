(*********************************************************************************************************************************)
(* NaturalDeductionCategory:                                                                                                     *)
(*                                                                                                                               *)
(*   Natural Deduction proofs form a category (under mild assumptions, see below)                                                *)
(*                                                                                                                               *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import NaturalDeduction.

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
Require Import InitialTerminal_ch2_2.

Open Scope nd_scope.
Open Scope pf_scope.

(* proofs form a category, with judgment-trees as the objects *)
Section Judgments_Category.

  Context {Judgment : Type}.
  Context {Rule     : forall (hypotheses:Tree ??Judgment)(conclusion:Tree ??Judgment), Type}.
  Context (nd_eqv   : @ND_Relation Judgment Rule).

  Notation "pf1 === pf2" := (@ndr_eqv _ _ nd_eqv _ _ pf1 pf2).

  (* there is a category whose objects are judgments and whose morphisms are proofs *)
  Instance Judgments_Category : Category (Tree ??Judgment) (fun h c => h /⋯⋯/ c) :=
  { id   := fun h          => nd_id _
  ; comp := fun a b c f g  => f ;; g
  ; eqv  := fun a b f g    => f === g
  }.
  intros; apply Build_Equivalence;
    [ unfold Reflexive; intros; reflexivity
    | unfold Symmetric; intros; symmetry; auto
    | unfold Transitive; intros; transitivity y; auto ].
  unfold Proper; unfold respectful; intros; simpl; apply ndr_comp_respects; auto.
  intros; apply ndr_comp_left_identity.
  intros; apply ndr_comp_right_identity.
  intros; apply ndr_comp_associativity.
  Defined.

  (* it is monoidal, with the judgment-tree-formation operator as its tensor *)
  Definition Judgments_Category_monoidal_endofunctor_fobj : Judgments_Category ×× Judgments_Category -> Judgments_Category :=
    fun xy => (fst_obj _ _ xy),,(snd_obj _ _ xy).
  Definition Judgments_Category_monoidal_endofunctor_fmor :
           forall a b, (a~~{Judgments_Category ×× Judgments_Category}~~>b) ->
           ((Judgments_Category_monoidal_endofunctor_fobj a)
           ~~{Judgments_Category}~~>
           (Judgments_Category_monoidal_endofunctor_fobj b)).
     intros.
     destruct a.
     destruct b.
     destruct X.
     simpl in *.
     exact (h**h0).
     Defined.
  Definition Judgments_Category_monoidal_endofunctor
  : Functor (Judgments_Category ×× Judgments_Category) Judgments_Category Judgments_Category_monoidal_endofunctor_fobj.
    refine {| fmor := Judgments_Category_monoidal_endofunctor_fmor |}; intros; simpl.
    abstract (destruct a; destruct b; destruct f; destruct f'; auto; destruct H; simpl in *; apply ndr_prod_respects; auto).
    abstract (destruct a; simpl in *; reflexivity).
    abstract (destruct a; destruct b; destruct c; destruct f; destruct g; symmetry; simpl in *; apply ndr_prod_preserves_comp).
    Defined.

  Definition jud_assoc_iso (a b c:Judgments_Category) : @Isomorphic _ _ Judgments_Category ((a,,b),,c) (a,,(b,,c)).
    refine
    {| iso_forward  := nd_assoc
     ; iso_backward := nd_cossa |};
    abstract (simpl; auto).
    Defined.
  Definition jud_cancelr_iso (a:Judgments_Category) : @Isomorphic _ _ Judgments_Category (a,,[]) a.
    refine
    {| iso_forward  := nd_cancelr
     ; iso_backward := nd_rlecnac |};
    abstract (simpl; auto).
    Defined.
  Definition jud_cancell_iso (a:Judgments_Category) : @Isomorphic _ _ Judgments_Category ([],,a) a.
    refine
    {| iso_forward  := nd_cancell
     ; iso_backward := nd_llecnac |};
    abstract (simpl; auto).
    Defined.

  Definition jud_mon_cancelr : (func_rlecnac [] >>>> Judgments_Category_monoidal_endofunctor) <~~~> functor_id Judgments_Category.
    refine {| ni_iso := fun x => jud_cancelr_iso x |}; intros; simpl.
    abstract (setoid_rewrite (ndr_prod_right_identity f);
              repeat setoid_rewrite ndr_comp_associativity;
              apply ndr_comp_respects; try reflexivity;
              symmetry;
              eapply transitivity; [ idtac | apply ndr_comp_right_identity ];
              apply ndr_comp_respects; try reflexivity; simpl; auto).
    Defined.
  Definition jud_mon_cancell : (func_llecnac [] >>>> Judgments_Category_monoidal_endofunctor) <~~~> functor_id Judgments_Category.
    eapply Build_NaturalIsomorphism.
    instantiate (1:=fun x => jud_cancell_iso x).
    abstract (intros; simpl;
              setoid_rewrite (ndr_prod_left_identity f);
              repeat setoid_rewrite ndr_comp_associativity;
              apply ndr_comp_respects; try reflexivity;
              symmetry;
              eapply transitivity; [ idtac | apply ndr_comp_right_identity ];
              apply ndr_comp_respects; try reflexivity; simpl; auto).
    Defined.
  Definition jud_mon_assoc_iso : forall X, 
      (((Judgments_Category_monoidal_endofunctor **** (functor_id _)) >>>>
        Judgments_Category_monoidal_endofunctor) X) ≅
       (func_cossa >>>> ((((functor_id _) **** Judgments_Category_monoidal_endofunctor) >>>>
         Judgments_Category_monoidal_endofunctor))) X.
    intros.
    destruct X as [a c].
    destruct a as [a b].
    exact (jud_assoc_iso a b c).
    Defined.
  Definition jud_mon_assoc   :
    ((Judgments_Category_monoidal_endofunctor **** (functor_id _)) >>>> Judgments_Category_monoidal_endofunctor)
    <~~~>
    func_cossa >>>> ((((functor_id _) **** Judgments_Category_monoidal_endofunctor) >>>> Judgments_Category_monoidal_endofunctor)).
    refine {| ni_iso := jud_mon_assoc_iso |}.
    intros.
    unfold hom in *.
    destruct A as [a1 a3]. destruct a1 as [a1 a2]. simpl in *.
    destruct B as [b1 b3]. destruct b1 as [b1 b2]. simpl in *.
    destruct f as [f1 f3]. destruct f1 as [f1 f2]. simpl in *.
    unfold hom in *.
    unfold ob in *.
    unfold functor_fobj; unfold fmor; unfold functor_product_fobj; unfold Judgments_Category_monoidal_endofunctor_fobj; simpl.
    setoid_rewrite ndr_prod_associativity.
    setoid_rewrite ndr_comp_associativity.
    setoid_rewrite ndr_comp_associativity.
    apply ndr_comp_respects; try reflexivity.
    etransitivity.
    symmetry.
    apply ndr_comp_right_identity.
    apply ndr_comp_respects; try reflexivity.
    apply ndr_structural_indistinguishable; auto.
    Defined.

  Instance Judgments_Category_monoidal : MonoidalCat _ _ Judgments_Category_monoidal_endofunctor [ ] :=
  { mon_cancelr := jud_mon_cancelr
  ; mon_cancell := jud_mon_cancell
  ; mon_assoc   := jud_mon_assoc   }.
    abstract
      (unfold functor_fobj; unfold fmor; unfold functor_product_fobj; unfold Judgments_Category_monoidal_endofunctor_fobj; simpl;
        apply Build_Pentagon; simpl; intros; apply ndr_structural_indistinguishable; auto).
    abstract
      (unfold functor_fobj; unfold fmor; unfold functor_product_fobj; unfold Judgments_Category_monoidal_endofunctor_fobj; simpl;
        apply Build_Triangle; simpl; intros; apply ndr_structural_indistinguishable; auto).
    Defined.

  Instance Judgments_Category_Terminal : Terminal Judgments_Category.
    refine {| one := [] ; drop := nd_weak' ; drop_unique := _ |}.
      abstract (intros; unfold eqv; simpl; apply ndr_void_proofs_irrelevant).
    Defined.

  Instance Judgments_Category_Diagonal : DiagonalCat Judgments_Category_monoidal.
    refine {| copy_nt := _ |}.
    intros.
    refine {| nt_component := nd_copy |}.
    intros.
    unfold hom in *; unfold ob in *; unfold eqv.
    simpl.
    rewrite ndr_prod_preserves_copy; auto.
    reflexivity.
    Defined.

  Instance Judgments_Category_CartesianCat : CartesianCat Judgments_Category_monoidal.
    refine {| car_terminal := Judgments_Category_Terminal ; car_diagonal := Judgments_Category_Diagonal
      ; car_one := iso_id [] |}
      ; intros; unfold hom; simpl
      ; unfold functor_fobj; unfold fmor; unfold functor_product_fobj; unfold Judgments_Category_monoidal_endofunctor_fobj; simpl.

    apply ndr_structural_indistinguishable; auto.
    apply nd_structural_comp; auto.
    apply nd_structural_comp; auto.
    unfold copy; simpl; apply nd_structural_copy; auto.
    apply nd_structural_prod; auto.
    apply nd_structural_comp; auto.
    apply weak'_structural.
    apply nd_structural_id0; auto.
    apply nd_structural_cancell; auto.

    apply ndr_structural_indistinguishable; auto.
    apply nd_structural_comp; auto.
    apply nd_structural_comp; auto.
    unfold copy; simpl; apply nd_structural_copy; auto.
    apply nd_structural_prod; auto.
    apply nd_structural_comp; auto.
    apply weak'_structural.
    apply nd_structural_id0; auto.
    apply nd_structural_cancelr; auto.
    Defined.

End Judgments_Category.

Close Scope pf_scope.
Close Scope nd_scope.
