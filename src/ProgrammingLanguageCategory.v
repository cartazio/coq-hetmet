(*********************************************************************************************************************************)
(* ProgrammingLanguageCategory                                                                                                   *)
(*                                                                                                                               *)
(*   The category Types(L)                                                                                                       *)
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
Require Import BinoidalCategories.
Require Import PreMonoidalCategories.
Require Import MonoidalCategories_ch7_8.
Require Import Coherence_ch7_8.
Require Import Enrichment_ch2_8.
Require Import RepresentableStructure_ch7_2.
Require Import FunctorCategories_ch7_7.

Require Import NaturalDeduction.
Require Import ProgrammingLanguage.
        Export ProgrammingLanguage.

Require Import NaturalDeductionCategory.

Open Scope nd_scope.
(* I am at a loss to explain why "auto" can't handle this *)
Ltac ndpc_tac :=
  match goal with
    | [ |- NDPredicateClosure ?P (?A ;; ?B) ] => apply ndpc_comp; ndpc_tac
    | [ |- NDPredicateClosure ?P (?A ** ?B) ] => apply ndpc_prod; ndpc_tac
    | _                                       => auto
  end.

(* this tactical searches the environment; setoid_rewrite doesn't seem to be able to do that properly sometimes *)
Ltac nd_swap_ltac P EQV :=
  match goal with
    [ |- context [ (?F ** nd_id _) ;; (nd_id _ ** ?G) ] ] => 
      set (@nd_swap _ _ EQV _ _ _ _ F G) as P
  end.

(* I still wish I knew why "Hint Constructors" doesn't work *)
Hint Extern 5 => apply snd_inert_initial.
Hint Extern 5 => apply snd_inert_cut.
Hint Extern 5 => apply snd_inert_structural.
Hint Extern 5 => apply cnd_inert_initial.
Hint Extern 5 => apply cnd_inert_cut.
Hint Extern 5 => apply cnd_inert_structural.
Hint Extern 5 => apply cnd_inert_cnd_ant_assoc.
Hint Extern 5 => apply cnd_inert_cnd_ant_cossa.
Hint Extern 5 => apply cnd_inert_cnd_ant_cancell.
Hint Extern 5 => apply cnd_inert_cnd_ant_cancelr.
Hint Extern 5 => apply cnd_inert_cnd_ant_llecnac.
Hint Extern 5 => apply cnd_inert_cnd_ant_rlecnac.
Hint Extern 5 => apply cnd_inert_se_expand_left.
Hint Extern 5 => apply cnd_inert_se_expand_right.

Hint Extern 2 (@Structural _ _ _ _ (@nd_id _ _ []   )) => simpl; auto.
Hint Extern 2 (@Structural _ _ _ _ (@nd_id _ _ [ _ ])) => simpl; auto.

Section ProgrammingLanguageCategory.

  Context {T    : Type}.               (* types of the language *)

  Context {Rule : Tree ??(@PLJudg T) -> Tree ??(@PLJudg T) -> Type}.
     Notation "cs |= ss" := (@sequent T cs ss) : pl_scope.

  Notation "H /⋯⋯/ C" := (ND Rule H C) : pl_scope.

  Open Scope pf_scope.
  Open Scope nd_scope.
  Open Scope pl_scope.

  Context (PL:@ProgrammingLanguage T Rule).

  (* category of judgments in a fixed type/coercion context *)
  Definition Judgments_cartesian := @Judgments_Category_CartesianCat _ Rule pl_eqv.

  Definition JudgmentsL          := Judgments_cartesian.

  Definition identityProof t : [] ~~{JudgmentsL}~~> [t |= t].
    unfold hom; simpl.
    apply snd_initial.
    Defined.

  Definition cutProof a b c : [a |= b],,[b |= c] ~~{JudgmentsL}~~> [a |= c].
    unfold hom; simpl.
    apply snd_cut.
    Defined.

  Instance TypesL : ECategory JudgmentsL (Tree ??T) (fun x y => [x|=y]) :=
  { eid   := identityProof
  ; ecomp := cutProof
  }.
    intros; apply (mon_commutative(MonoidalCat:=JudgmentsL)).
    intros; apply (mon_commutative(MonoidalCat:=JudgmentsL)).
    abstract (intros; unfold identityProof; unfold cutProof; simpl; eapply cndr_inert; auto; apply PL).
    abstract (intros; unfold identityProof; unfold cutProof; simpl; eapply cndr_inert; auto; apply PL).
    abstract (intros; unfold identityProof; unfold cutProof; simpl; eapply cndr_inert;
                [ apply PL | idtac | idtac ]; apply ndpc_comp; auto).
    Defined.

  Instance Types_first c : EFunctor TypesL TypesL (fun x => x,,c ) :=
    { efunc := fun x y => cnd_expand_right(ContextND:=pl_cnd) x y c }.
    intros; apply (mon_commutative(MonoidalCat:=JudgmentsL)).
    abstract (intros; simpl; apply (cndr_inert pl_cnd); auto).
    abstract (intros; unfold ehom; unfold comp; simpl; unfold cutProof;
              rewrite <- (@ndr_prod_preserves_comp _ _ PL _ _ (cnd_expand_right _ _ c) _ _ (nd_id1 (b|=c0))
                          _ (nd_id1 (a,,c |= b,,c))  _ (cnd_expand_right _ _ c));
              setoid_rewrite (@ndr_comp_right_identity _ _ PL _ [a,, c |= b,, c]);
              setoid_rewrite (@ndr_comp_left_identity  _ _ PL [b |= c0]);
              simpl; eapply cndr_inert; [ apply PL | auto | auto ]).
    Defined.

  Instance Types_second c : EFunctor TypesL TypesL (fun x => c,,x) :=
    { efunc := fun x y => ((@cnd_expand_left _ _ _ _ _ _ x y c)) }.
    intros; apply (mon_commutative(MonoidalCat:=JudgmentsL)).
    abstract (intros; simpl; apply (cndr_inert pl_cnd); auto).
    intros; unfold ehom; unfold comp; simpl; unfold cutProof;
    abstract (rewrite <- (@ndr_prod_preserves_comp _ _ PL _ _ (cnd_expand_left _ _ c) _ _ (nd_id1 (b|=c0))
                          _ (nd_id1 (c,,a |= c,,b))  _ (cnd_expand_left _ _ c));
              setoid_rewrite (@ndr_comp_right_identity _ _ PL _ [c,,a |= c,,b]);
              setoid_rewrite (@ndr_comp_left_identity  _ _ PL [b |= c0]);
              simpl; eapply cndr_inert; [ apply PL | auto | auto ]).
    Defined.

  Instance Types_binoidal : EBinoidalCat TypesL (@T_Branch _) :=
  { ebc_first  := Types_first
  ; ebc_second := Types_second
  }.

  Instance Types_assoc_iso a b c : Isomorphic(C:=TypesL) ((a,,b),,c) (a,,(b,,c)) :=
  { iso_forward  := snd_initial _ ;; cnd_ant_cossa _ a b c
  ; iso_backward := snd_initial _ ;; cnd_ant_assoc _ a b c
  }.
    abstract (simpl; eapply cndr_inert; unfold identityProof; [ apply PL | idtac | idtac ]; ndpc_tac).
    abstract (simpl; eapply cndr_inert; unfold identityProof; [ apply PL | idtac | idtac ]; ndpc_tac).
    Defined.

  Instance Types_cancelr_iso a : Isomorphic(C:=TypesL) (a,,[]) a :=
  { iso_forward  := snd_initial _ ;; cnd_ant_rlecnac _ a
  ; iso_backward := snd_initial _ ;; cnd_ant_cancelr _ a
  }.
    abstract (simpl; eapply cndr_inert; unfold identityProof; [ apply PL | idtac | idtac ]; ndpc_tac).
    abstract (simpl; eapply cndr_inert; unfold identityProof; [ apply PL | idtac | idtac ]; ndpc_tac).
    Defined.

  Instance Types_cancell_iso a : Isomorphic(C:=TypesL) ([],,a) a :=
    { iso_forward  := snd_initial _ ;; cnd_ant_llecnac _ a
    ; iso_backward := snd_initial _ ;; cnd_ant_cancell _ a
    }.
    abstract (simpl; eapply cndr_inert; unfold identityProof; [ apply PL | idtac | idtac ]; ndpc_tac).
    abstract (simpl; eapply cndr_inert; unfold identityProof; [ apply PL | idtac | idtac ]; ndpc_tac).
    Defined.

  Lemma coincide' : nd_llecnac === nd_rlecnac.
    set (coincide (pmon_triangle(PreMonoidalCat:=(Judgments_Category_premonoidal PL)))) as q'.
    set (isos_forward_equal_then_backward_equal _ _ q') as qq.
    apply qq.
    Qed.

  Lemma Types_assoc_lemma : ∀a b X Y : TypesL,
      ∀f : X ~~{ TypesL }~~> Y,
      #(Types_assoc_iso a X b) >>> (Types_first b >>>> Types_second a) \ f ~~
      (Types_second a >>>> Types_first b) \ f >>> #(Types_assoc_iso a Y b).
    intros.
    Opaque nd_id.
      simpl.
      Transparent nd_id.
    unfold ehom.

    nd_swap_ltac p PL.
      setoid_rewrite p.
      clear p.

    repeat setoid_rewrite (@ndr_comp_associativity _ Rule PL).

    setoid_rewrite (@nd_prod_split_left  _ Rule PL _ _ _ []).
    setoid_rewrite (@nd_prod_split_left  _ Rule PL _ _ _ []).
    setoid_rewrite (@nd_prod_split_right _ Rule PL _ _ _ []).
    setoid_rewrite (@nd_prod_split_right _ Rule PL _ _ _ []).

    setoid_rewrite (@ndr_comp_associativity _ Rule PL).
    setoid_rewrite (@ndr_comp_associativity _ Rule PL).
    setoid_rewrite <- (@ndr_comp_associativity _ Rule PL).

    set (ni_commutes' (jud_mon_cancelr PL) f) as q.
      simpl in q.
      setoid_rewrite <- q. 
      clear q.

    set (ni_commutes' (jud_mon_cancell PL) f) as q.      
      simpl in q.
      setoid_rewrite coincide' in q.
      setoid_rewrite <- q.
      clear q.

    setoid_rewrite (@ndr_comp_associativity _ Rule PL).
      apply ndr_comp_respects; try reflexivity.

    apply (cndr_inert pl_cnd); auto; ndpc_tac; auto.
    Qed.

  Instance Types_assoc a b : Types_second a >>>> Types_first b <~~~> Types_first b >>>> Types_second a :=
    { ni_iso := fun c => Types_assoc_iso a c b }.
    apply Types_assoc_lemma.
    Defined.

  Lemma Types_assoc_ll_lemma : 
    ∀a b X Y : TypesL,
    ∀f : X ~~{ TypesL }~~> Y,
    #(Types_assoc_iso a b X) >>> (Types_second b >>>> Types_second a) \ f ~~
    Types_second (a,, b) \ f >>> #(Types_assoc_iso a b Y).

    intros.
    Opaque nd_id.
    simpl.
    Transparent nd_id.
    unfold ehom.
    nd_swap_ltac p PL.
    setoid_rewrite p.
    clear p.

    setoid_rewrite (@nd_prod_split_left  _ Rule PL _ _ _ []).
    setoid_rewrite (@nd_prod_split_left  _ Rule PL _ _ _ []).
    setoid_rewrite (@nd_prod_split_right _ Rule PL _ _ _ []).

    repeat setoid_rewrite (@ndr_comp_associativity _ Rule PL).
    setoid_rewrite <- (@ndr_comp_associativity _ Rule PL).

    set (ni_commutes' (jud_mon_cancelr PL) f) as q.
    Opaque nd_id.
    simpl in q.
    setoid_rewrite <- q.

    clear q.
    set (ni_commutes' (jud_mon_cancell PL) f) as q.      
    simpl in q.
    set (coincide (pmon_triangle(PreMonoidalCat:=(Judgments_Category_premonoidal PL)))) as q'.
    set (isos_forward_equal_then_backward_equal _ _ q') as qq.
    simpl in qq.
    setoid_rewrite qq in q.
    clear q' qq.
    setoid_rewrite <- q.

    setoid_rewrite (@ndr_comp_associativity _ Rule PL).
    apply ndr_comp_respects; try reflexivity.

    Transparent nd_id.
    apply (cndr_inert pl_cnd); auto; ndpc_tac.
    Qed.

  Instance Types_assoc_ll a b : Types_second (a,,b) <~~~> Types_second b >>>> Types_second a :=
    { ni_iso := fun c => Types_assoc_iso a b c }.
    apply Types_assoc_ll_lemma.
    Defined.

  Lemma Types_assoc_rr_lemma :
    ∀a b A B : TypesL,
    ∀f : A ~~{ TypesL }~~> B,
    #(Types_assoc_iso A a b) ⁻¹ >>> (Types_first a >>>> Types_first b) \ f ~~
    Types_first (a,, b) \ f >>> #(Types_assoc_iso B a b) ⁻¹.
    intros.
    Opaque nd_id.
    simpl.
    Transparent nd_id.

    rename A into X.
    rename B into Y.
    unfold ehom.
    nd_swap_ltac p PL.
    setoid_rewrite p.
    clear p.

    setoid_rewrite (@nd_prod_split_left  _ Rule PL _ _ _ []).
    setoid_rewrite (@nd_prod_split_left  _ Rule PL _ _ _ []).
    setoid_rewrite (@nd_prod_split_right _ Rule PL _ _ _ []).

    repeat setoid_rewrite (@ndr_comp_associativity _ Rule PL).
    setoid_rewrite <- (@ndr_comp_associativity _ Rule PL).

    set (ni_commutes' (jud_mon_cancelr PL) f) as q.
    Opaque nd_id.
    simpl in q.
    setoid_rewrite <- q.

    clear q.
    set (ni_commutes' (jud_mon_cancell PL) f) as q.      
    simpl in q.
    set (coincide (pmon_triangle(PreMonoidalCat:=(Judgments_Category_premonoidal PL)))) as q'.
    set (isos_forward_equal_then_backward_equal _ _ q') as qq.
    simpl in qq.
    setoid_rewrite qq in q.
    clear q' qq.
    setoid_rewrite <- q.

    setoid_rewrite (@ndr_comp_associativity _ Rule PL).
    apply ndr_comp_respects; try reflexivity.

    Transparent nd_id.
    apply (cndr_inert pl_cnd); auto; ndpc_tac.
    Qed.

  Instance Types_assoc_rr a b : Types_first (a,,b) <~~~> Types_first a >>>> Types_first b :=
    { ni_iso := fun c => iso_inv _ _ (Types_assoc_iso c a b) }.
    apply Types_assoc_rr_lemma.
    Defined.

  Lemma Types_cancelr_lemma :
    ∀A B : TypesL,
    ∀f : A ~~{ TypesL }~~> B,
    #(Types_cancelr_iso A) >>> functor_id TypesL \ f ~~
    Types_first [] \ f >>> #(Types_cancelr_iso B).
    intros.
    Opaque nd_id.
    simpl.
    unfold ehom.
    nd_swap_ltac p PL.
    setoid_rewrite p.
    setoid_rewrite (@nd_prod_split_right _ Rule PL _ _ _ []).
    repeat setoid_rewrite (@ndr_comp_associativity _ Rule PL).
    setoid_rewrite <- (@ndr_comp_associativity _ Rule PL).

    set (ni_commutes' (jud_mon_cancelr PL) f) as q.
    Opaque nd_id.
    simpl in q.
    setoid_rewrite <- q.
    clear q.

    set (ni_commutes' (jud_mon_cancell PL) f) as q.      
    simpl in q.
    set (coincide (pmon_triangle(PreMonoidalCat:=(Judgments_Category_premonoidal PL)))) as q'.
    set (isos_forward_equal_then_backward_equal _ _ q') as qq.
    simpl in qq.
    setoid_rewrite qq in q.
    clear q' qq.
    setoid_rewrite <- q.

    setoid_rewrite (@ndr_comp_associativity _ Rule PL).
    apply ndr_comp_respects; try reflexivity.
    Transparent nd_id.
    simpl.
    apply (cndr_inert pl_cnd); auto; ndpc_tac.
    Qed.

  Instance Types_cancelr   : Types_first [] <~~~> functor_id _ :=
    { ni_iso := Types_cancelr_iso }.
    apply Types_cancelr_lemma.
    Defined.

  Lemma Types_cancell_lemma :
    ∀A B : TypesL,
    ∀f : A ~~{ TypesL }~~> B,
    #(Types_cancell_iso A) >>> functor_id TypesL \ f ~~
    Types_second [] \ f >>> #(Types_cancell_iso B).
    intros.
    Opaque nd_id.
    simpl.
    unfold ehom.
    nd_swap_ltac p PL.
    setoid_rewrite p.
    setoid_rewrite (@nd_prod_split_right _ Rule PL _ _ _ []).
    repeat setoid_rewrite (@ndr_comp_associativity _ Rule PL).
    setoid_rewrite <- (@ndr_comp_associativity _ Rule PL).

    set (ni_commutes' (jud_mon_cancelr PL) f) as q.
    Opaque nd_id.
    simpl in q.
    setoid_rewrite <- q.
    clear q.

    set (ni_commutes' (jud_mon_cancell PL) f) as q.      
    simpl in q.
    set (coincide (pmon_triangle(PreMonoidalCat:=(Judgments_Category_premonoidal PL)))) as q'.
    set (isos_forward_equal_then_backward_equal _ _ q') as qq.
    simpl in qq.
    setoid_rewrite qq in q.
    clear q' qq.
    setoid_rewrite <- q.
    setoid_rewrite (@ndr_comp_associativity _ Rule PL).

    apply ndr_comp_respects; try reflexivity.
    Transparent nd_id.
    simpl.
    apply (cndr_inert pl_cnd); auto; ndpc_tac.
    Qed.

  Instance Types_cancell   : Types_second [] <~~~> functor_id _ :=
    { ni_iso := Types_cancell_iso }.
    apply Types_cancell_lemma.
    Defined.

  Lemma TypesL_assoc_central a b c : CentralMorphism(H:=Types_binoidal) #((Types_assoc a b) c).
    intros.
      apply Build_CentralMorphism.
      intros.
      unfold bin_obj.
      unfold ebc_bobj.
      Opaque nd_id.
      simpl.
      unfold ehom.
      nd_swap_ltac p PL.
      setoid_rewrite p.
      clear p.
      setoid_rewrite (@nd_prod_split_left  _ Rule PL _ _ _ []).
      setoid_rewrite (@nd_prod_split_right _ Rule PL _ _ _ []).
      repeat setoid_rewrite (@ndr_comp_associativity _ Rule PL).
      setoid_rewrite <- (@ndr_comp_associativity _ Rule PL).

      set (ni_commutes' (jud_mon_cancelr PL) g) as q.
      Opaque nd_id.
      simpl in q.
      setoid_rewrite <- q.
      clear q.

      set (ni_commutes' (jud_mon_cancell PL) g) as q.      
      simpl in q.
      set (coincide (pmon_triangle(PreMonoidalCat:=(Judgments_Category_premonoidal PL)))) as q'.
      set (isos_forward_equal_then_backward_equal _ _ q') as qq.
      simpl in qq.
      setoid_rewrite qq in q.
      clear q' qq.
      setoid_rewrite <- q.

      setoid_rewrite (@ndr_comp_associativity _ Rule PL).
      apply ndr_comp_respects.
      reflexivity.
      
      Transparent nd_id.
      apply (cndr_inert pl_cnd); auto; ndpc_tac.

      Opaque nd_id.
      intros.
      unfold bin_obj.
      unfold ebc_bobj.
      simpl.
      unfold ehom.
      symmetry.
      nd_swap_ltac p PL.
      setoid_rewrite p.
      clear p.
      setoid_rewrite (@nd_prod_split_left  _ Rule PL _ _ _ []).
      setoid_rewrite (@nd_prod_split_right _ Rule PL _ _ _ []).
      repeat setoid_rewrite (@ndr_comp_associativity _ Rule PL).
      setoid_rewrite <- (@ndr_comp_associativity _ Rule PL).

      set (ni_commutes' (jud_mon_cancelr PL) g) as q.
      Opaque nd_id.
      simpl in q.
      setoid_rewrite <- q.
      clear q.

      set (ni_commutes' (jud_mon_cancell PL) g) as q.      
      simpl in q.
      set (coincide (pmon_triangle(PreMonoidalCat:=(Judgments_Category_premonoidal PL)))) as q'.
      set (isos_forward_equal_then_backward_equal _ _ q') as qq.
      simpl in qq.
      setoid_rewrite qq in q.
      clear q' qq.
      setoid_rewrite <- q.

      setoid_rewrite (@ndr_comp_associativity _ Rule PL).
      apply ndr_comp_respects.
      reflexivity.
      
      Transparent nd_id.
      apply (cndr_inert pl_cnd); auto; ndpc_tac.
      Qed.

  Lemma TypesL_cancell_central a : CentralMorphism(H:=Types_binoidal) #(Types_cancell a).
    intros.
      apply Build_CentralMorphism.
      Opaque nd_id.
      intros.
      unfold bin_obj.
      unfold ebc_bobj.
      simpl.
      unfold ehom.
      nd_swap_ltac p PL.
      setoid_rewrite p.
      clear p.
      setoid_rewrite (@nd_prod_split_left  _ Rule PL _ _ _ []).
      setoid_rewrite (@nd_prod_split_right _ Rule PL _ _ _ []).
      repeat setoid_rewrite (@ndr_comp_associativity _ Rule PL).
      setoid_rewrite <- (@ndr_comp_associativity _ Rule PL).

      set (ni_commutes' (jud_mon_cancelr PL) g) as q.
      Opaque nd_id.
      simpl in q.
      setoid_rewrite <- q.
      clear q.

      set (ni_commutes' (jud_mon_cancell PL) g) as q.      
      simpl in q.
      set (coincide (pmon_triangle(PreMonoidalCat:=(Judgments_Category_premonoidal PL)))) as q'.
      set (isos_forward_equal_then_backward_equal _ _ q') as qq.
      simpl in qq.
      setoid_rewrite qq in q.
      clear q' qq.
      setoid_rewrite <- q.

      setoid_rewrite (@ndr_comp_associativity _ Rule PL).
      apply ndr_comp_respects.
      reflexivity.
      
      Transparent nd_id.
      apply (cndr_inert pl_cnd); auto; ndpc_tac.

      Opaque nd_id.
      intros.
      unfold bin_obj.
      unfold ebc_bobj.
      simpl.
      unfold ehom.
      symmetry.
      nd_swap_ltac p PL.
      setoid_rewrite p.
      clear p.
      setoid_rewrite (@nd_prod_split_left  _ Rule PL _ _ _ []).
      setoid_rewrite (@nd_prod_split_right _ Rule PL _ _ _ []).
      repeat setoid_rewrite (@ndr_comp_associativity _ Rule PL).
      setoid_rewrite <- (@ndr_comp_associativity _ Rule PL).

      set (ni_commutes' (jud_mon_cancelr PL) g) as q.
      Opaque nd_id.
      simpl in q.
      setoid_rewrite <- q.
      clear q.

      set (ni_commutes' (jud_mon_cancell PL) g) as q.      
      simpl in q.
      set (coincide (pmon_triangle(PreMonoidalCat:=(Judgments_Category_premonoidal PL)))) as q'.
      set (isos_forward_equal_then_backward_equal _ _ q') as qq.
      simpl in qq.
      setoid_rewrite qq in q.
      clear q' qq.
      setoid_rewrite <- q.

      setoid_rewrite (@ndr_comp_associativity _ Rule PL).
      apply ndr_comp_respects.
      reflexivity.
      
      Transparent nd_id.
      apply (cndr_inert pl_cnd); auto; ndpc_tac.
      Qed.

  Lemma TypesL_cancelr_central a : CentralMorphism(H:=Types_binoidal) #(Types_cancelr a).
    intros.
      apply Build_CentralMorphism.
      Opaque nd_id.
      intros.
      unfold bin_obj.
      unfold ebc_bobj.
      simpl.
      unfold ehom.
      nd_swap_ltac p PL.
      setoid_rewrite p.
      clear p.
      setoid_rewrite (@nd_prod_split_left  _ Rule PL _ _ _ []).
      setoid_rewrite (@nd_prod_split_right _ Rule PL _ _ _ []).
      repeat setoid_rewrite (@ndr_comp_associativity _ Rule PL).
      setoid_rewrite <- (@ndr_comp_associativity _ Rule PL).

      set (ni_commutes' (jud_mon_cancelr PL) g) as q.
      Opaque nd_id.
      simpl in q.
      setoid_rewrite <- q.
      clear q.

      set (ni_commutes' (jud_mon_cancell PL) g) as q.      
      simpl in q.
      set (coincide (pmon_triangle(PreMonoidalCat:=(Judgments_Category_premonoidal PL)))) as q'.
      set (isos_forward_equal_then_backward_equal _ _ q') as qq.
      simpl in qq.
      setoid_rewrite qq in q.
      clear q' qq.
      setoid_rewrite <- q.

      setoid_rewrite (@ndr_comp_associativity _ Rule PL).
      apply ndr_comp_respects.
      reflexivity.
      
      Transparent nd_id.
      apply (cndr_inert pl_cnd); auto; ndpc_tac.

      Opaque nd_id.
      intros.
      unfold bin_obj.
      unfold ebc_bobj.
      simpl.
      unfold ehom.
      symmetry.
      nd_swap_ltac p PL.
      setoid_rewrite p.
      clear p.
      setoid_rewrite (@nd_prod_split_left  _ Rule PL _ _ _ []).
      setoid_rewrite (@nd_prod_split_right _ Rule PL _ _ _ []).
      repeat setoid_rewrite (@ndr_comp_associativity _ Rule PL).
      setoid_rewrite <- (@ndr_comp_associativity _ Rule PL).

      set (ni_commutes' (jud_mon_cancelr PL) g) as q.
      Opaque nd_id.
      simpl in q.
      setoid_rewrite <- q.
      clear q.

      set (ni_commutes' (jud_mon_cancell PL) g) as q.      
      simpl in q.
      set (coincide (pmon_triangle(PreMonoidalCat:=(Judgments_Category_premonoidal PL)))) as q'.
      set (isos_forward_equal_then_backward_equal _ _ q') as qq.
      simpl in qq.
      setoid_rewrite qq in q.
      clear q' qq.
      setoid_rewrite <- q.

      setoid_rewrite (@ndr_comp_associativity _ Rule PL).
      apply ndr_comp_respects.
      reflexivity.
      
      Transparent nd_id.
      apply (cndr_inert pl_cnd); auto; ndpc_tac.
      Qed.

  Instance TypesL_PreMonoidal : PreMonoidalCat Types_binoidal [] :=
    { pmon_assoc    := Types_assoc
    ; pmon_cancell  := Types_cancell
    ; pmon_cancelr  := Types_cancelr
    ; pmon_assoc_rr := Types_assoc_rr
    ; pmon_assoc_ll := Types_assoc_ll
    }.
    abstract (apply Build_Pentagon; intros; simpl; eapply cndr_inert; try apply PL; ndpc_tac).
    abstract (apply Build_Triangle; intros; simpl; eapply cndr_inert; try apply PL; ndpc_tac).
    intros; simpl; reflexivity.
    intros; simpl; reflexivity.
    apply TypesL_assoc_central.
    apply TypesL_cancelr_central.
    apply TypesL_cancell_central.
    Defined.

End ProgrammingLanguageCategory.

