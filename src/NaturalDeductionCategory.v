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

Open Scope nd_scope.
Open Scope pf_scope.

(* proofs form a category, with judgment-trees as the objects *)
Section Judgments_Category.

  Context {Judgment : Type}.
  Context {Rule     : forall (hypotheses:Tree ??Judgment)(conclusion:Tree ??Judgment), Type}.
  Context (nd_eqv   : @ND_Relation Judgment Rule).

  (* actually you can use any type as the objects, so long as you give a mapping from that type to judgments *)
  Context {Ob       : Type}.
  Context (ob2judgment : Ob -> Judgment).
  Coercion ob2judgment : Ob >-> Judgment.

  Notation "pf1 === pf2" := (@ndr_eqv _ _ nd_eqv _ _ pf1 pf2).

  Instance Judgments_Category
    : Category (Tree ??Ob) (fun h c => (mapOptionTree ob2judgment h) /⋯⋯/ (mapOptionTree ob2judgment c)) :=
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

  Definition Judgments_Category_monoidal_endofunctor_fobj : Judgments_Category ×× Judgments_Category -> Judgments_Category :=
    (fun xy =>
     match xy with
     | pair_obj x y => T_Branch x y
     end).
  Definition Judgments_Category_monoidal_endofunctor_fmor :
           forall a b, (a~~{Judgments_Category ×× Judgments_Category}~~>b) ->
           ((Judgments_Category_monoidal_endofunctor_fobj a)
           ~~{Judgments_Category}~~>
           (Judgments_Category_monoidal_endofunctor_fobj b)).
     intros.
     destruct a.
     destruct b.
     destruct X.
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
    apply (@Build_Isomorphic _ _ Judgments_Category _ _
      (@nd_assoc _ Rule  (mapOptionTree ob2judgment a) (mapOptionTree ob2judgment b) (mapOptionTree ob2judgment c)
        : (a,, b),, c ~~{Judgments_Category}~~> a,, (b,, c))
      (@nd_cossa _ Rule  (mapOptionTree ob2judgment a) (mapOptionTree ob2judgment b) (mapOptionTree ob2judgment c)
        : a,, (b,, c) ~~{Judgments_Category}~~> (a,, b),, c)); simpl; auto.
    Defined.
  Definition jud_cancelr_iso (a:Judgments_Category) : @Isomorphic _ _ Judgments_Category (a,,[]) a.
    apply (@Build_Isomorphic _ _ Judgments_Category _ _
      (@nd_cancelr _ Rule (mapOptionTree ob2judgment a) : a,,[] ~~{Judgments_Category}~~> a)
      (@nd_rlecnac _ Rule (mapOptionTree ob2judgment a) : a     ~~{Judgments_Category}~~> a,,[])); simpl; auto.
    Defined.
  Definition jud_cancell_iso (a:Judgments_Category) : @Isomorphic _ _ Judgments_Category ([],,a) a.
    apply (@Build_Isomorphic _ _ Judgments_Category _ _
      (@nd_cancell _ Rule (mapOptionTree ob2judgment a) : [],,a ~~{Judgments_Category}~~> a)
      (@nd_llecnac _ Rule (mapOptionTree ob2judgment a) : a     ~~{Judgments_Category}~~> [],,a)); simpl; auto.
    Defined.

  Definition jud_mon_cancelr : (func_rlecnac [] >>>> Judgments_Category_monoidal_endofunctor) <~~~> functor_id Judgments_Category.
    refine {| ni_iso := fun x => jud_cancelr_iso x |}; intros; simpl.
    setoid_rewrite (ndr_prod_right_identity f).
    repeat setoid_rewrite ndr_comp_associativity.
    apply ndr_comp_respects; try reflexivity.
    symmetry.
    eapply transitivity; [ idtac | apply ndr_comp_right_identity ].
    apply ndr_comp_respects; try reflexivity; simpl; auto.
    Defined.
  Definition jud_mon_cancell : (func_llecnac [] >>>> Judgments_Category_monoidal_endofunctor) <~~~> functor_id Judgments_Category.
    eapply Build_NaturalIsomorphism.
    instantiate (1:=fun x => jud_cancell_iso x).
    intros; simpl.
    setoid_rewrite (ndr_prod_left_identity f).
    repeat setoid_rewrite ndr_comp_associativity.
    apply ndr_comp_respects; try reflexivity.
    symmetry.
    eapply transitivity; [ idtac | apply ndr_comp_right_identity ].
    apply ndr_comp_respects; try reflexivity; simpl; auto.
    Defined.
  Definition jud_mon_assoc_iso :
    forall X, 
      (((Judgments_Category_monoidal_endofunctor **** (functor_id _)) >>>> Judgments_Category_monoidal_endofunctor) X) ≅
  (func_cossa >>>> ((((functor_id _) **** Judgments_Category_monoidal_endofunctor) >>>> Judgments_Category_monoidal_endofunctor))) X.
    intros.
    destruct X as [a c].
    destruct a as [a b].
    apply (jud_assoc_iso a b c).
    Defined.
  Definition jud_mon_assoc   :
    ((Judgments_Category_monoidal_endofunctor **** (functor_id _)) >>>> Judgments_Category_monoidal_endofunctor)
    <~~~>
    func_cossa >>>> ((((functor_id _) **** Judgments_Category_monoidal_endofunctor) >>>> Judgments_Category_monoidal_endofunctor)).
    refine {| ni_iso := jud_mon_assoc_iso |}.
    intros.
    destruct A as [a1 a3]. destruct a1 as [a1 a2].
    destruct B as [b1 b3]. destruct b1 as [b1 b2].
    destruct f as [f1 f3]. destruct f1 as [f1 f2].
    simpl.
    setoid_rewrite ndr_prod_associativity.
    setoid_rewrite ndr_comp_associativity.
    setoid_rewrite ndr_comp_associativity.
    apply ndr_comp_respects; try reflexivity.
    symmetry.
    eapply transitivity; [ idtac | apply ndr_comp_right_identity ].
    apply ndr_comp_respects; try reflexivity; simpl; auto.
    Defined.

  Instance Judgments_Category_monoidal : MonoidalCat _ _ Judgments_Category_monoidal_endofunctor [ ] :=
  { mon_cancelr := jud_mon_cancelr
  ; mon_cancell := jud_mon_cancell
  ; mon_assoc   := jud_mon_assoc   }.
    apply Build_Pentagon; simpl; intros; apply ndr_structural_indistinguishable; auto.
    apply Build_Triangle; simpl; intros; apply ndr_structural_indistinguishable; auto.
    Defined.

  Instance Judgments_Category_CartesianCat : CartesianCat Judgments_Category_monoidal.
    admit.
    Defined.

  (* Given some mapping "rep" that turns a (Tree ??T) intoto Judgment,
   * this asserts that we have sensible structural rules with respect
   * to that mapping.  Doing all of this "with respect to a mapping"
   * lets us avoid duplicating code for both the antecedent and
   * succedent of sequent deductions. *)
  Class TreeStructuralRules  {T:Type}(rep:Tree ??T -> Judgment) :=
  { tsr_eqv           : @ND_Relation Judgment Rule where "pf1 === pf2" := (@ndr_eqv _ _ tsr_eqv _ _ pf1 pf2)
  ; tsr_ant_assoc     : forall {a b c}, Rule [rep ((a,,b),,c)]     [rep ((a,,(b,,c)))]
  ; tsr_ant_cossa     : forall {a b c}, Rule [rep (a,,(b,,c))]     [rep (((a,,b),,c))]
  ; tsr_ant_cancell   : forall {a    }, Rule [rep (  [],,a  )]     [rep (        a  )]
  ; tsr_ant_cancelr   : forall {a    }, Rule [rep (a,,[]    )]     [rep (        a  )]
  ; tsr_ant_llecnac   : forall {a    }, Rule [rep (      a  )]     [rep (  [],,a    )]
  ; tsr_ant_rlecnac   : forall {a    }, Rule [rep (      a  )]     [rep (  a,,[]    )]
  }.


  (* Structure ExpressionAlgebra (sig:Signature) := *)

End Judgments_Category.

Close Scope pf_scope.
Close Scope nd_scope.
