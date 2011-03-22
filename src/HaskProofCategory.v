(*********************************************************************************************************************************)
(* HaskProofCategory:                                                                                                            *)
(*                                                                                                                               *)
(*    Natural Deduction proofs of the well-typedness of a Haskell term form a category                                           *)
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
Require Import MonoidalCategories_ch7_8.
Require Import Coherence_ch7_8.

Require Import FreydCategories.


Section HaskProofCategory.

  (* This proof will work for any dynamic semantics you like, so
   * long as those semantics are an ND_Relation (associativity,
   * neutrality, etc) *)
  Context (dynamic_semantics   : @ND_Relation _ Rule).

  Section SystemFC_Category.

    Context {Γ:TypeEnv}
            {Δ:CoercionEnv Γ}.

    Definition Context := Tree ??(LeveledHaskType Γ ★).

    Notation "a |= b" := (Γ >> Δ > a |- b).

    (* category of judgments in a fixed type/coercion context *)
    Definition JudgmentsFC :=
      @Judgments_Category_monoidal _ Rule dynamic_semantics (UJudg Γ Δ) UJudg2judg.

    Definition identityProof t : [] ~~{JudgmentsFC}~~> [t |= t].
      unfold hom; simpl.
      admit.
      Defined.

    Definition cutProof a b c : [a |= b],,[b |= c] ~~{JudgmentsFC}~~> [a |= c].
      unfold hom; simpl.
      admit.
      Defined.

    Definition TypesFC : ECategory JudgmentsFC Context (fun x y => [Γ >> Δ > x |- y]).
      refine
      {| eid   := identityProof
       ; ecomp := cutProof
      |}; intros.
      apply MonoidalCat_all_central.
      apply MonoidalCat_all_central.
      admit.
      admit.
      admit.
      Defined.

    Definition TypesEnrichedInJudgments : Enrichment.
      refine {| enr_c := TypesFC |}.
      Defined.
   
(*
    Definition TwoLevelLanguage L2 :=
    { L1 : _ &
      Reification (TypesEnrichedInJudgments L1) (TypesEnrichedInJudgments L2) }

    Inductive NLevelLanguage : nat -> Language -> Type :=
    | NLevelLanguage_zero : forall lang,    NLevelLanguage O lang
    | NLevelLanguage_succ : forall L1 L2 n, TwoLevelLanguage L1 L2 -> NLevelLanguage n L1 -> NLevelLanguage (S n) L2

    Definition OmegaLevelLanguage : Language -> Type :=
      forall n:nat, NLevelLanguage n L.
*)

    
    (* The full subcategory of SystemFC(Γ,Δ) consisting only of judgments involving types at a fixed level.  Note that
     * code types are still permitted! *)
    Section SingleLevel.
      Context (lev:HaskLevel Γ).

      Inductive ContextAtLevel : Context -> Prop :=
        | contextAtLevel_nil    :               ContextAtLevel []
        | contextAtLevel_leaf   : forall τ,     ContextAtLevel [τ @@ lev]
        | contextAtLevel_branch : forall b1 b2, ContextAtLevel b1 -> ContextAtLevel b2 -> ContextAtLevel (b1,,b2).

      Inductive JudgmentsAtLevel : JudgmentsFC -> Prop :=
        | judgmentsAtLevel_nil    : JudgmentsAtLevel []
        | judgmentsAtLevel_leaf   : forall c1 c2, ContextAtLevel c1 -> ContextAtLevel c2 -> JudgmentsAtLevel [c1 |= c2]
        | judgmentsAtLevel_branch : forall j1 j2, JudgmentsAtLevel j1 -> JudgmentsAtLevel j2 -> JudgmentsAtLevel (j1,,j2).
  
      Definition JudgmentsFCAtLevel := FullSubcategory JudgmentsFC JudgmentsAtLevel.
      Definition TypesFCAtLevel     := FullSubcategory TypesFC     ContextAtLevel.
    End SingleLevel.

  End SystemFC_Category.

  Implicit Arguments TypesFC [ ].

  Definition Types_first c : EFunctor (TypesFC nil nil) (TypesFC nil nil) (fun x => x,,c ).
    admit.
    Defined.
  Definition Types_second c : EFunctor (TypesFC nil nil) (TypesFC nil nil) (fun x => c,,x ).
    admit.
    Defined.

  Definition Types_binoidal : BinoidalCat (TypesFC nil nil) (@T_Branch _).
    refine
      {| bin_first  := Types_first
       ; bin_second := Types_second
       |}.
    Defined.

  Definition Types_premonoidal : PreMonoidalCat Types_binoidal [].
    admit.
    Defined.

(*
  Definition ArrowInProgrammingLanguage :=
    FreydCategory Types_premonoidal Types_premonoidal.

  FlatSubCategory

  InitialGArrowsAllowFlattening

  SystemFCa

  PCF

  SystemFCa_two_level
  SystemFCa_initial_GArrow
  

*)

    
(*
    Section EscBrak_Functor.
      Context
        (past:@Past V)
        (n:V)
        (Σ₁:Tree ??(@LeveledHaskType V)).
    
      Definition EscBrak_Functor_Fobj
        : SystemFC_Cat_Flat ((Σ₁,n)::past) -> SystemFC_Cat past
        := mapOptionTree (fun q:Tree ??(@CoreType V) * Tree ??(@CoreType V) =>
          let (a,s):=q in (Σ₁,,(``a)^^^n,[`<[ n |- encodeTypeTree_flat s ]>])).
   
      Definition append_brak
      : forall {c}, ND_ML
          (mapOptionTree (ob2judgment_flat ((⟨Σ₁,n⟩) :: past))                        c )
          (mapOptionTree (ob2judgment                   past )  (EscBrak_Functor_Fobj c)).
        intros.
        unfold ND_ML.
        unfold EscBrak_Functor_Fobj.
        rewrite mapOptionTree_comp.
        simpl in *.
        apply nd_replicate.
        intro o; destruct o.
        apply nd_rule.
        apply MLRBrak.
        Defined.
    
      Definition prepend_esc
      : forall {h}, ND_ML
          (mapOptionTree (ob2judgment                  past )  (EscBrak_Functor_Fobj h))
          (mapOptionTree (ob2judgment_flat ((⟨Σ₁,n⟩) :: past))                        h ).
        intros.
        unfold ND_ML.
        unfold EscBrak_Functor_Fobj.
        rewrite mapOptionTree_comp.
        simpl in *.
        apply nd_replicate.
        intro o; destruct o.
        apply nd_rule.
        apply MLREsc.
        Defined.
    
      Definition EscBrak_Functor_Fmor
        : forall a b (f:a~~{SystemFC_Cat_Flat ((Σ₁,n)::past)}~~>b), 
          (EscBrak_Functor_Fobj a)~~{SystemFC_Cat past}~~>(EscBrak_Functor_Fobj b).
        intros.
        eapply nd_comp.
        apply prepend_esc.
        eapply nd_comp.
        eapply Flat_to_ML.
        apply f.
        apply append_brak.
        Defined.
            
      Lemma esc_then_brak_is_id : forall a,
       ndr_eqv(ND_Relation:=ml_dynamic_semantics V) (nd_comp prepend_esc append_brak)
         (nd_id (mapOptionTree (ob2judgment past) (EscBrak_Functor_Fobj a))).
         admit.
         Qed.
    
      Lemma brak_then_esc_is_id : forall a,
       ndr_eqv(ND_Relation:=ml_dynamic_semantics V) (nd_comp append_brak prepend_esc)
         (nd_id (mapOptionTree (ob2judgment_flat (((Σ₁,n)::past))) a)).
         admit.
         Qed.
    
      Instance EscBrak_Functor
        : Functor (SystemFC_Cat_Flat ((Σ₁,n)::past)) (SystemFC_Cat past) EscBrak_Functor_Fobj :=
        { fmor := fun a b f => EscBrak_Functor_Fmor a b f }.
        intros; unfold EscBrak_Functor_Fmor; simpl in *.
          apply ndr_comp_respects; try reflexivity.
          apply ndr_comp_respects; try reflexivity.
          auto.
        intros; unfold EscBrak_Functor_Fmor; simpl in *.
          set (@ndr_comp_left_identity _ _ (ml_dynamic_semantics V)) as q.
          setoid_rewrite q.
          apply esc_then_brak_is_id.
        intros; unfold EscBrak_Functor_Fmor; simpl in *.
          set (@ndr_comp_associativity _ _ (ml_dynamic_semantics V)) as q.
          repeat setoid_rewrite q.
          apply ndr_comp_respects; try reflexivity.
          apply ndr_comp_respects; try reflexivity.
          repeat setoid_rewrite <- q.
          apply ndr_comp_respects; try reflexivity.
          setoid_rewrite brak_then_esc_is_id.
          clear q.
          set (@ndr_comp_left_identity _ _ (fc_dynamic_semantics V)) as q.
          setoid_rewrite q.
          reflexivity.
        Defined.
  
    End EscBrak_Functor.
  


  Ltac rule_helper_tactic' :=
    match goal with
    | [ H : ?A = ?A |- _ ] => clear H
    | [ H : [?A] = [] |- _ ] => inversion H; clear H
    | [ H : [] = [?A] |- _ ] => inversion H; clear H
    | [ H : ?A,,?B = [] |- _ ] => inversion H; clear H
    | [ H : ?A,,?B = [?Y] |- _ ] => inversion H; clear H
    | [ H: ?A :: ?B = ?B |- _ ] => apply symmetry in H; apply list_cannot_be_longer_than_itself in H; destruct H
    | [ H: ?B = ?A :: ?B |- _ ] => apply list_cannot_be_longer_than_itself in H; destruct H
    | [ H: ?A :: ?C :: ?B = ?B |- _ ] => apply symmetry in H; apply list_cannot_be_longer_than_itself' in H; destruct H
    | [ H: ?B = ?A :: ?C :: ?B |- _ ] => apply list_cannot_be_longer_than_itself' in H; destruct H
(*  | [ H : Sequent T |- _ ] => destruct H *)
(*  | [ H : ?D = levelize ?C (?A |= ?B) |- _ ] => inversion H; clear H*)
    | [ H : [?A] = [?B] |- _ ] => inversion H; clear H
    | [ H : [] = mapOptionTree ?B ?C |- _ ] => apply mapOptionTree_on_nil in H; subst
    | [ H : [?A] = mapOptionTree ?B ?C |- _ ] => destruct C as [C|]; simpl in H; [ | inversion H ]; destruct C; simpl in H; simpl
    | [ H : ?A,,?B = mapOptionTree ?C ?D |- _ ] => destruct D as [D|] ; [destruct D|idtac]; simpl in H; inversion H
    end.

  Lemma fixit : forall a b f c1 c2, (@mapOptionTree a b f c1),,(mapOptionTree f c2) = mapOptionTree f (c1,,c2).
    admit.
    Defined.

  Lemma grak a b f c : @mapOptionTree a b f c = [] -> [] = c.
    admit.
    Qed.

  Definition append_brak_to_id : forall {c},
  @ND_FC V
      (mapOptionTree (ob2judgment ((⟨Σ₁,n⟩) :: past))  c )
      (mapOptionTree (ob2judgment past)  (EscBrak_Functor_Fobj c)).
  admit.
  Defined.

  Definition append_brak : forall {h c}
    (pf:@ND_FC V
      h
      (mapOptionTree (ob2judgment ((⟨Σ₁,n⟩) :: past))  c )),
    @ND_FC V
       h
      (mapOptionTree (ob2judgment past)  (EscBrak_Functor_Fobj c)).
    
      refine (fix append_brak h c nd {struct nd} :=
       ((match nd
            as nd'
            in @ND _ _ H C
            return
            (H=h) ->
            (C=mapOptionTree (ob2judgment ((⟨Σ₁,n⟩) :: past)) c) -> 
            ND_FC h (mapOptionTree (ob2judgment past) (EscBrak_Functor_Fobj c))
          with
          | nd_id0                     => let case_nd_id0     := tt in _
          | nd_id1     h               => let case_nd_id1     := tt in _
          | nd_weak    h               => let case_nd_weak    := tt in _
          | nd_copy    h               => let case_nd_copy    := tt in _
          | nd_prod    _ _ _ _ lpf rpf => let case_nd_prod    := tt in _
          | nd_comp    _ _ _   top bot => let case_nd_comp    := tt in _
          | nd_rule    _ _     rule    => let case_nd_rule    := tt in _
          | nd_cancell _               => let case_nd_cancell := tt in _
          | nd_cancelr _               => let case_nd_cancelr := tt in _
          | nd_llecnac _               => let case_nd_llecnac := tt in _
          | nd_rlecnac _               => let case_nd_rlecnac := tt in _
          | nd_assoc   _ _ _           => let case_nd_assoc   := tt in _
          | nd_cossa   _ _ _           => let case_nd_cossa   := tt in _
        end) (refl_equal _) (refl_equal _)
       ));
       simpl in *; intros; subst; simpl in *; try (repeat (rule_helper_tactic' || subst)); subst; simpl in *.
       destruct case_nd_id0. apply nd_id0.
       destruct case_nd_id1. apply nd_rule. destruct p. apply RBrak.
       destruct case_nd_weak. apply nd_weak.

       destruct case_nd_copy.
         (*
         destruct c; try destruct o; simpl in *; try rule_helper_tactic'; try destruct p; try rule_helper_tactic'.
         inversion H0; subst.
         simpl.*)
         idtac.
         clear H0.
         admit.

       destruct case_nd_prod.
         eapply nd_prod.
         apply (append_brak _ _ lpf).
         apply (append_brak _ _ rpf).

       destruct case_nd_comp.
         apply append_brak in bot.
         apply (nd_comp top bot).

       destruct case_nd_cancell.
         eapply nd_comp; [ apply nd_cancell | idtac ].
         apply append_brak_to_id.

       destruct case_nd_cancelr.
         eapply nd_comp; [ apply nd_cancelr | idtac ].
         apply append_brak_to_id.

       destruct case_nd_llecnac.
         eapply nd_comp; [ idtac | apply nd_llecnac ].
         apply append_brak_to_id.

       destruct case_nd_rlecnac.
         eapply nd_comp; [ idtac | apply nd_rlecnac ].
         apply append_brak_to_id.

       destruct case_nd_assoc.
         eapply nd_comp; [ apply nd_assoc | idtac ].
         repeat rewrite fixit.
         apply append_brak_to_id.

       destruct case_nd_cossa.
         eapply nd_comp; [ idtac | apply nd_cossa ].
         repeat rewrite fixit.
         apply append_brak_to_id.

       destruct case_nd_rule
  


    Defined.
    
  Definition append_brak {h c} : forall
      pf:@ND_FC V
        (fixify Γ ((⟨n, Σ₁ ⟩) :: past)                       h )
        c,
      @ND_FC V
        (fixify Γ                past  (EscBrak_Functor_Fobj h))
        c.
    admit.
    Defined.
*)
End HaskProofCategory.