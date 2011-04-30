(*********************************************************************************************************************************)
(* HaskFlattener:                                                                                                           *)
(*                                                                                                                               *)
(*    The Flattening Functor.                                                                                                    *)
(*                                                                                                                               *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import NaturalDeduction.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import HaskKinds.
Require Import HaskCoreTypes.
Require Import HaskLiteralsAndTyCons.
Require Import HaskStrongTypes.
Require Import HaskProof.
Require Import NaturalDeduction.
Require Import NaturalDeductionCategory.

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
Require Import BinoidalCategories.
Require Import PreMonoidalCategories.
Require Import MonoidalCategories_ch7_8.
Require Import Coherence_ch7_8.

Require Import HaskStrongTypes.
Require Import HaskStrong.
Require Import HaskProof.
Require Import HaskStrongToProof.
Require Import HaskProofToStrong.
Require Import ProgrammingLanguage.
Require Import HaskProgrammingLanguage.
Require Import PCF.

Open Scope nd_scope.

(*
 *  The flattening transformation.  Currently only TWO-level languages are
 *  supported, and the level-1 sublanguage is rather limited.
 *
 *  This file abuses terminology pretty badly.  For purposes of this file,
 *  "PCF" means "the level-1 sublanguage" and "FC" (aka System FC) means 
 *  the whole language (level-0 language including bracketed level-1 terms)
 *)
Section HaskFlattener.

  Context {Γ:TypeEnv}.
  Context {Δ:CoercionEnv Γ}.
  Context {ec:HaskTyVar Γ ★}.

  Lemma unlev_lemma : forall (x:Tree ??(HaskType Γ ★)) lev, x = mapOptionTree unlev (x @@@ lev).
    intros.
    rewrite <- mapOptionTree_compose.
    simpl.
    induction x.
    destruct a; simpl; auto.
    simpl.
    rewrite IHx1 at 1.
    rewrite IHx2 at 1.
    reflexivity.
    Qed.

  Context (ga_rep      : Tree ??(HaskType Γ ★) -> HaskType Γ ★ ).
  Context (ga_type     : HaskType Γ ★ -> HaskType Γ ★ -> HaskType Γ ★).

  (*Notation "a ~~~~> b" := (ND Rule [] [ Γ > Δ > a |- b ]) (at level 20).*)
  Notation "a ~~~~> b" := (ND (OrgR Γ Δ) [] [ (a , b) ]) (at level 20).

  Lemma magic : forall a b c,
    ([]                   ~~~~> [ga_type a b @@ nil]) ->
    ([ga_type b c @@ nil] ~~~~> [ga_type a c @@ nil]).
    admit.
    Qed.

  Context (ga_lit      : ∀ lit, [] ~~~~> [ga_type (ga_rep   []   )      (ga_rep [literalType lit])@@ nil]).
  Context (ga_id       : ∀ σ,   [] ~~~~> [ga_type (ga_rep   σ    )      (ga_rep σ                )@@ nil]).
  Context (ga_cancell  : ∀ c  , [] ~~~~> [ga_type (ga_rep ([],,c))      (ga_rep c                )@@ nil]).
  Context (ga_cancelr  : ∀ c  , [] ~~~~> [ga_type (ga_rep (c,,[]))      (ga_rep c                )@@ nil]).
  Context (ga_uncancell: ∀ c  , [] ~~~~> [ga_type (ga_rep  c     )      (ga_rep ([],,c)          )@@ nil]).
  Context (ga_uncancelr: ∀ c  , [] ~~~~> [ga_type (ga_rep  c     )      (ga_rep (c,,[])          )@@ nil]).
  Context (ga_assoc    : ∀ a b c,[] ~~~~> [ga_type (ga_rep ((a,,b),,c))  (ga_rep (a,,(b,,c))      )@@ nil]).
  Context (ga_unassoc  : ∀ a b c,[] ~~~~> [ga_type (ga_rep ( a,,(b,,c))) (ga_rep ((a,,b),,c))      @@ nil]).
  Context (ga_swap     : ∀ a b, [] ~~~~> [ga_type (ga_rep (a,,b) )      (ga_rep (b,,a)           )@@ nil]).
  Context (ga_copy     : ∀ a  , [] ~~~~> [ga_type (ga_rep  a     )      (ga_rep (a,,a)           )@@ nil]).
  Context (ga_drop     : ∀ a  , [] ~~~~> [ga_type (ga_rep  a     )      (ga_rep []               )@@ nil]).
  Context (ga_first    : ∀ a b c,
    [ga_type (ga_rep a) (ga_rep b) @@nil] ~~~~> [ga_type (ga_rep (a,,c)) (ga_rep (b,,c)) @@nil]).
  Context (ga_second   : ∀ a b c,
    [ga_type (ga_rep a) (ga_rep b) @@nil] ~~~~> [ga_type (ga_rep (c,,a)) (ga_rep (c,,b)) @@nil]).
  Context (ga_comp     : ∀ a b c,
    ([ga_type (ga_rep a) (ga_rep b) @@nil],,[ga_type (ga_rep b) (ga_rep c) @@nil])
    ~~~~>
    [ga_type (ga_rep a) (ga_rep c) @@nil]).

  Definition guestJudgmentAsGArrowType (lt:PCFJudg Γ ec) : HaskType Γ ★ :=
    match lt with
      (x,y) => (ga_type (ga_rep x) (ga_rep y)) 
    end.

  Definition obact (X:Tree ??(PCFJudg Γ ec)) : Tree ??(LeveledHaskType Γ ★) :=
    mapOptionTree guestJudgmentAsGArrowType X @@@ nil.

  Hint Constructors Rule_Flat.
  Context {ndr:@ND_Relation _ Rule}.

  (*
   * Here it is, what you've all been waiting for!  When reading this,
   * it might help to have the definition for "Inductive ND" (see
   * NaturalDeduction.v) handy as a cross-reference.
   *)
  Hint Constructors Rule_Flat.
  Definition FlatteningFunctor_fmor
    : forall h c,
      (ND (PCFRule Γ Δ ec) h c) ->
      ((obact h)~~~~>(obact c)).

    set (@nil (HaskTyVar Γ ★)) as lev.

    unfold hom; unfold ob; unfold ehom; simpl; unfold pmon_I; unfold obact; intros.

    induction X; simpl.

    (* the proof from no hypotheses of no conclusions (nd_id0) becomes RVoid *)
    apply nd_rule; apply (org_fc Γ Δ [] [(_,_)] (RVoid _ _)). apply Flat_RVoid.

    (* the proof from hypothesis X of conclusion X (nd_id1) becomes RVar *)
    apply nd_rule; apply (org_fc _ _ [] [(_,_)] (RVar _ _ _ _)). apply Flat_RVar.

    (* the proof from hypothesis X of no conclusions (nd_weak) becomes RWeak;;RVoid *)
    eapply nd_comp;
      [ idtac
      | eapply nd_rule
      ; eapply (org_fc  _ _ [(_,_)] [(_,_)] (RArrange _ _ _ _ _ (RWeak _)))
      ; auto ].
      eapply nd_rule.
      eapply (org_fc _ _ [] [(_,_)] (RVoid _ _)); auto. apply Flat_RVoid.
      apply Flat_RArrange.

    (* the proof from hypothesis X of two identical conclusions X,,X (nd_copy) becomes RVar;;RJoin;;RCont *)
    eapply nd_comp; [ idtac | eapply nd_rule; eapply (org_fc _ _ [(_,_)] [(_,_)] (RArrange _ _ _ _ _ (RCont _))) ].
      eapply nd_comp; [ apply nd_llecnac | idtac ].
      set (snd_initial(SequentND:=pl_snd(ProgrammingLanguage:=SystemFCa Γ Δ))
        (mapOptionTree (guestJudgmentAsGArrowType) h @@@ lev)) as q.
      eapply nd_comp.
      eapply nd_prod.
      apply q.
      apply q.
      apply nd_rule. 
      eapply (org_fc _ _ ([(_,_)],,[(_,_)]) [(_,_)] (RJoin _ _ _ _ _ _ )).
      destruct h; simpl.
      destruct o.
      simpl.
      apply Flat_RJoin.
      apply Flat_RJoin.
      apply Flat_RJoin.
      apply Flat_RArrange.

    (* nd_prod becomes nd_llecnac;;nd_prod;;RJoin *)
    eapply nd_comp.
      apply (nd_llecnac ;; nd_prod IHX1 IHX2).
      apply nd_rule.
      eapply (org_fc _ _ ([(_,_)],,[(_,_)]) [(_,_)] (RJoin _ _ _ _ _ _ )).
      apply (Flat_RJoin Γ Δ (mapOptionTree guestJudgmentAsGArrowType h1 @@@ nil)
       (mapOptionTree guestJudgmentAsGArrowType h2 @@@ nil)
       (mapOptionTree guestJudgmentAsGArrowType c1 @@@ nil)
       (mapOptionTree guestJudgmentAsGArrowType c2 @@@ nil)).

    (* nd_comp becomes pl_subst (aka nd_cut) *)
    eapply nd_comp.
      apply (nd_llecnac ;; nd_prod IHX1 IHX2).
      clear IHX1 IHX2 X1 X2.
      apply (@snd_cut _ _ _ _ (pl_snd(ProgrammingLanguage:=SystemFCa Γ Δ))). 

    (* nd_cancell becomes RVar;;RuCanL *)
    eapply nd_comp;
      [ idtac | eapply nd_rule; apply (org_fc _ _ [(_,_)] [(_,_)] (RArrange _ _ _ _ _ (RuCanL _))) ].
      apply (snd_initial(SequentND:=pl_cnd(ProgrammingLanguage:=(SystemFCa Γ Δ)))).
      apply Flat_RArrange.

    (* nd_cancelr becomes RVar;;RuCanR *)
    eapply nd_comp;
      [ idtac | eapply nd_rule; apply (org_fc _ _ [(_,_)] [(_,_)] (RArrange _ _ _ _ _ (RuCanR _))) ].
      apply (snd_initial(SequentND:=pl_cnd(ProgrammingLanguage:=(SystemFCa Γ Δ)))).
      apply Flat_RArrange.

    (* nd_llecnac becomes RVar;;RCanL *)
    eapply nd_comp;
      [ idtac | eapply nd_rule; apply (org_fc _ _ [(_,_)] [(_,_)] (RArrange _ _ _ _ _ (RCanL _))) ].
      apply (snd_initial(SequentND:=pl_cnd(ProgrammingLanguage:=(SystemFCa Γ Δ)))).
      apply Flat_RArrange.

    (* nd_rlecnac becomes RVar;;RCanR *)
    eapply nd_comp;
      [ idtac | eapply nd_rule; apply (org_fc _ _ [(_,_)] [(_,_)] (RArrange _ _ _ _ _ (RCanR _))) ].
      apply (snd_initial(SequentND:=pl_cnd(ProgrammingLanguage:=(SystemFCa Γ Δ)))).
      apply Flat_RArrange.

    (* nd_assoc becomes RVar;;RAssoc *)
    eapply nd_comp;
      [ idtac | eapply nd_rule; apply (org_fc _ _ [(_,_)] [(_,_)] (RArrange _ _ _ _ _ (RAssoc _ _ _))) ].
      apply (snd_initial(SequentND:=pl_cnd(ProgrammingLanguage:=(SystemFCa Γ Δ)))).
      apply Flat_RArrange.

    (* nd_cossa becomes RVar;;RCossa *)
    eapply nd_comp;
      [ idtac | eapply nd_rule; apply (org_fc _ _ [(_,_)] [(_,_)] (RArrange _ _ _ _ _ (RCossa _ _ _))) ].
      apply (snd_initial(SequentND:=pl_cnd(ProgrammingLanguage:=(SystemFCa Γ Δ)))).
      apply Flat_RArrange.

      destruct r as [r rp].
      rename h into h'.
      rename c into c'.
      rename r into r'.

      refine (match rp as R in @Rule_PCF _ _ _ H C _
                return
                ND (OrgR Γ Δ) []
                [sequent (mapOptionTree guestJudgmentAsGArrowType H @@@ nil)
                  (mapOptionTree guestJudgmentAsGArrowType C @@@ nil)]
                with
                | PCF_RArrange         h c r q          => let case_RURule        := tt in _
                | PCF_RLit             lit              => let case_RLit          := tt in _
                | PCF_RNote            Σ τ   n          => let case_RNote         := tt in _
                | PCF_RVar             σ                => let case_RVar          := tt in _
                | PCF_RLam             Σ tx te          => let case_RLam          := tt in _
                | PCF_RApp             Σ tx te   p      => let case_RApp          := tt in _
                | PCF_RLet             Σ σ₁ σ₂   p      => let case_RLet          := tt in _
                | PCF_RJoin    b c d e          => let case_RJoin := tt in _
                | PCF_RVoid                       => let case_RVoid   := tt in _
              (*| PCF_RCase            T κlen κ θ l x   => let case_RCase         := tt in _*)
              (*| PCF_RLetRec          Σ₁ τ₁ τ₂ lev     => let case_RLetRec       := tt in _*)
              end); simpl in *.
      clear rp h' c' r'.

      rewrite (unlev_lemma h (ec::nil)).
      rewrite (unlev_lemma c (ec::nil)).
      destruct case_RURule.
        refine (match q as Q in Arrange H C
                return
                H=(h @@@ (ec :: nil)) ->
                C=(c @@@ (ec :: nil)) ->
                ND (OrgR Γ Δ) []
                [sequent
                  [ga_type (ga_rep (mapOptionTree unlev H)) (ga_rep r) @@ nil ]
                  [ga_type (ga_rep (mapOptionTree unlev C)) (ga_rep r) @@ nil ] ]
                  with
          | RLeft   a b c r => let case_RLeft  := tt in _
          | RRight  a b c r => let case_RRight := tt in _
          | RCanL     b     => let case_RCanL  := tt in _
          | RCanR     b     => let case_RCanR  := tt in _
          | RuCanL    b     => let case_RuCanL := tt in _
          | RuCanR    b     => let case_RuCanR := tt in _
          | RAssoc    b c d => let case_RAssoc := tt in _
          | RCossa    b c d => let case_RCossa := tt in _
          | RExch     b c   => let case_RExch  := tt in _
          | RWeak     b     => let case_RWeak  := tt in _
          | RCont     b     => let case_RCont  := tt in _
          | RComp a b c f g => let case_RComp  := tt in _
        end (refl_equal _) (refl_equal _));
        intros; simpl in *;
        subst;
        try rewrite <- unlev_lemma in *.

      destruct case_RCanL.
        apply magic.
        apply ga_uncancell.
        
      destruct case_RCanR.
        apply magic.
        apply ga_uncancelr.

      destruct case_RuCanL.
        apply magic.
        apply ga_cancell.

      destruct case_RuCanR.
        apply magic.
        apply ga_cancelr.

      destruct case_RAssoc.
        apply magic.
        apply ga_assoc.
        
      destruct case_RCossa.
        apply magic.
        apply ga_unassoc.

      destruct case_RExch.
        apply magic.
        apply ga_swap.
        
      destruct case_RWeak.
        apply magic.
        apply ga_drop.
        
      destruct case_RCont.
        apply magic.
        apply ga_copy.
        
      destruct case_RLeft.
        apply magic.
        (*apply ga_second.*)
        admit.
        
      destruct case_RRight.
        apply magic.
        (*apply ga_first.*)
        admit.

      destruct case_RComp.
        apply magic.
        (*apply ga_comp.*)
        admit.

      destruct case_RLit.
        apply ga_lit.

      (* hey cool, I figured out how to pass CoreNote's through... *)
      destruct case_RNote.
        eapply nd_comp.
        eapply nd_rule.
        eapply (org_fc _ _ [] [(_,_)] (RVar _ _ _ _)) . auto.
        apply Flat_RVar.
        apply nd_rule.
        apply (org_fc _ _ [(_,_)] [(_,_)] (RNote _ _ _ _ _ n)). auto.
        apply Flat_RNote.
        
      destruct case_RVar.
        apply ga_id.

      (*
       *   class GArrow g (**) u => GArrowApply g (**) u (~>) where
       *     ga_applyl    :: g (x**(x~>y)   ) y
       *     ga_applyr    :: g (   (x~>y)**x) y
       *   
       *   class GArrow g (**) u => GArrowCurry g (**) u (~>) where
       *     ga_curryl    :: g (x**y) z  ->  g x (y~>z)
       *     ga_curryr    :: g (x**y) z  ->  g y (x~>z)
       *)
      destruct case_RLam.
        (* GArrowCurry.ga_curry *)
        admit.

      destruct case_RApp.
        (* GArrowApply.ga_apply *)
        admit.

      destruct case_RLet.
        admit.

      destruct case_RVoid.
        apply ga_id.

      destruct case_RJoin.
        (* this assumes we want effects to occur in syntactically-left-to-right order *)
        admit.
        Defined.

(*
  Instance FlatteningFunctor {Γ}{Δ}{ec} : Functor (JudgmentsL (PCF Γ Δ ec)) (TypesL (SystemFCa Γ Δ)) (obact) :=
    { fmor := FlatteningFunctor_fmor }.
    Admitted.

  Definition ReificationFunctor Γ Δ : Functor (JudgmentsL _ _ (PCF n Γ Δ)) SystemFCa' (mapOptionTree brakifyJudg).
    refine {| fmor := ReificationFunctor_fmor Γ Δ |}; unfold hom; unfold ob; simpl ; intros.
    Admitted.

  Definition PCF_SMME (n:nat)(Γ:TypeEnv)(Δ:CoercionEnv Γ) : ProgrammingLanguageSMME.
    refine {| plsmme_pl := PCF n Γ Δ |}.
    admit.
    Defined.

  Definition SystemFCa_SMME (n:nat)(Γ:TypeEnv)(Δ:CoercionEnv Γ) : ProgrammingLanguageSMME.
    refine {| plsmme_pl := SystemFCa n Γ Δ |}.
    admit.
    Defined.

  Definition ReificationFunctorMonoidal n : MonoidalFunctor (JudgmentsN n) (JudgmentsN (S n)) (ReificationFunctor n).
    admit.
    Defined.

  (* 5.1.4 *)
  Definition PCF_SystemFCa_two_level n Γ Δ : TwoLevelLanguage (PCF_SMME n Γ Δ) (SystemFCa_SMME (S n) Γ Δ).
    admit.
    Defined.
*)
  (*  ... and the retraction exists *)

End HaskFlattener.

