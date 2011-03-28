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

Require Import HaskStrongTypes.
Require Import HaskStrong.
Require Import HaskProof.
Require Import HaskStrongToProof.
Require Import HaskProofToStrong.
Require Import ProgrammingLanguage.

Section HaskProofCategory.

  Definition unitType {Γ} : RawHaskType Γ ★.
    admit.
    Defined.

  Definition brakifyType {Γ} (v:HaskTyVar Γ ★)(lt:LeveledHaskType Γ ★) : LeveledHaskType Γ ★ :=
    match lt with
      t @@ l => HaskBrak v t @@ l
    end.
 
  Definition brakifyu {Γ}{Δ}(v:HaskTyVar Γ ★)(j:UJudg Γ Δ) : UJudg Γ Δ :=
    match j with
      mkUJudg Σ τ =>
        Γ >> Δ > mapOptionTree (brakifyType v) Σ |- mapOptionTree (brakifyType v) τ
    end.

  Definition mkEsc {Γ}{Δ}(j:Tree ??(UJudg Γ Δ)) v h
    : ND Rule
    (mapOptionTree (@UJudg2judg Γ Δ) h)
    (mapOptionTree (fun j => @UJudg2judg Γ Δ (brakifyu v j)) h).
    admit.
    Defined.

  Definition mkBrak {Γ}{Δ}(j:Tree ??(UJudg Γ Δ)) v h
    : ND Rule
    (mapOptionTree (fun j => @UJudg2judg Γ Δ (brakifyu v j)) h)
    (mapOptionTree (@UJudg2judg Γ Δ           ) h).
    admit.
    Defined.

  Context (ndr_systemfc:@ND_Relation _ Rule).

  Open Scope nd_scope.

  (* Rules allowed in PCF; i.e. rules we know how to turn into GArrows *)
  (* Rule_PCF consists of the rules allowed in flat PCF: everything except
     * AppT, AbsT, AppC, AbsC, Cast, Global, and some Case statements *)
  Inductive Rule_PCF {Γ:TypeEnv}{Δ:CoercionEnv Γ} : forall {h}{c}, Rule h c -> Type :=
  | PCF_RURule           : ∀ h c r            ,  Rule_PCF (RURule Γ Δ  h c r)
  | PCF_RLit             : ∀ Σ τ              ,  Rule_PCF (RLit Γ Δ Σ τ  )
  | PCF_RNote            : ∀ Σ τ l n          ,  Rule_PCF (RNote Γ Δ Σ τ l n)
  | PCF_RVar             : ∀ σ               l,  Rule_PCF (RVar Γ Δ  σ         l)
  | PCF_RLam             : ∀ Σ tx te    q     ,  Rule_PCF (RLam Γ Δ  Σ tx te      q )
  | PCF_RApp             : ∀ Σ tx te   p     l,  Rule_PCF (RApp Γ Δ  Σ tx te   p l)
  | PCF_RLet             : ∀ Σ σ₁ σ₂   p     l,  Rule_PCF (RLet Γ Δ  Σ σ₁ σ₂   p l)
  | PCF_RBindingGroup    : ∀ q a b c d e      ,  Rule_PCF (RBindingGroup q a b c d e)
  | PCF_RCase            : ∀ T κlen κ θ l x   ,  Rule_PCF (RCase Γ Δ T κlen κ θ l x)   (* FIXME: only for boolean and int *)
  | PCF_REmptyGroup      : ∀ q a              ,  Rule_PCF (REmptyGroup q a)
  | PCF_RLetRec          : ∀ Σ₁ τ₁ τ₂ lev     ,  Rule_PCF (RLetRec Γ Δ Σ₁ τ₁ τ₂ lev).
  Implicit Arguments Rule_PCF [ ].

  Definition PCFR Γ Δ h c := { r:_ & Rule_PCF Γ Δ h c r }.

  (* An organized deduction has been reorganized into contiguous blocks whose
   * hypotheses (if any) and conclusion have the same Γ and Δ and a fixed nesting depth.  The boolean
   * indicates if non-PCF rules have been used *)
  Inductive OrgR : bool -> nat -> forall Γ Δ, Tree ??(UJudg Γ Δ) -> Tree ??(UJudg Γ Δ) -> Type :=

  | org_pcf       : forall n Γ Δ h c b,
    PCFR Γ Δ (mapOptionTree UJudg2judg h) (mapOptionTree UJudg2judg c) -> OrgR b n Γ Δ h c

  | org_fc        : forall n Γ Δ h c,
    ND Rule (mapOptionTree UJudg2judg h) (mapOptionTree UJudg2judg c) -> OrgR true n Γ Δ h c

  | org_nest      : forall n Γ Δ h c b v,
    OrgR b    n  Γ Δ h c ->
    OrgR b (S n) _ _ (mapOptionTree (brakifyu v) h) (mapOptionTree (brakifyu v) c)
  . 

  Definition OrgND b n Γ Δ := ND (OrgR b n Γ Δ).

  (* any proof in organized form can be "dis-organized" *)
  Definition unOrgR b n Γ Δ : forall h c, OrgR b n Γ Δ h c ->
    ND Rule (mapOptionTree (@UJudg2judg Γ Δ) h) (mapOptionTree (@UJudg2judg Γ Δ) c).

    intros.

    induction X.
      apply nd_rule.
      destruct p.
      apply x.

    apply n0.

    rewrite <- mapOptionTree_compose.
      rewrite <- mapOptionTree_compose.
      eapply nd_comp.
      apply (mkBrak h).
      eapply nd_comp; [ idtac |  apply (mkEsc c) ].
      apply IHX.
      Defined.

    Definition unOrgND b n Γ Δ h c : 
      ND (OrgR b n Γ Δ) h c -> ND Rule (mapOptionTree (@UJudg2judg Γ Δ) h) (mapOptionTree (@UJudg2judg Γ Δ) c)
      := nd_map' (@UJudg2judg Γ Δ) (unOrgR b n Γ Δ).
    
    Instance OrgNDR b n Γ Δ : @ND_Relation _ (OrgR b n Γ Δ) :=
    { ndr_eqv := fun a b f g => (unOrgND _ _ _ _ _ _ f) === (unOrgND _ _ _ _ _ _ g) }.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      Defined.

      (*
    Hint Constructors Rule_Flat.

    Definition SystemFC_SC n : @SequentCalculus _ (RuleSystemFCa n) _ (mkJudg Γ Δ).
      apply Build_SequentCalculus.
      intro a.
      induction a.
      destruct a.
      apply nd_rule.
      destruct l.
      apply sfc_flat with (r:=RVar _ _ _ _).
      auto.
      apply nd_rule.
      apply sfc_flat with (r:=REmptyGroup _ _).
      auto.
      eapply nd_comp; [ apply nd_llecnac | idtac ].
      eapply nd_comp; [ eapply nd_prod | idtac ].
      apply IHa1.
      apply IHa2.
      apply nd_rule.
      apply sfc_flat with (r:=RBindingGroup _ _ _ _ _ _ ).
      auto.
      Defined.

    Existing Instance SystemFC_SC.

    Lemma systemfc_cut n : ∀a b c,
           ND (RuleSystemFCa n) ([Γ > Δ > a |- b],, [Γ > Δ > b |- c]) [Γ > Δ > a |- c]. 
      intros.
      admit.
      Defined.

    Lemma systemfc_cutrule n
      : @CutRule _ (RuleSystemFCa n) _ (mkJudg Γ Δ) (ndr_systemfc n) (SystemFC_SC n).
      apply Build_CutRule with (nd_cut:=systemfc_cut n).
      admit.
      admit.
      admit.
      Defined.

    Definition systemfc_left n a b c : ND (RuleSystemFCa n) [Γ > Δ > b |- c] [Γ > Δ > a,, b |- a,, c].
      eapply nd_comp; [ apply nd_llecnac | idtac ].
      eapply nd_comp; [ eapply nd_prod | idtac ].
      Focus 3.
      apply nd_rule.
      apply sfc_flat with (r:=RBindingGroup _ _ _ _ _ _ ).
      auto.
      idtac.
      apply nd_seq_reflexive.
      apply nd_id.
      Defined.

    Definition systemfc_right n a b c : ND (RuleSystemFCa n) [Γ > Δ > b |- c] [Γ > Δ > b,,a |- c,,a].
      eapply nd_comp; [ apply nd_rlecnac | idtac ].
      eapply nd_comp; [ eapply nd_prod | idtac ].
      apply nd_id.
      apply (nd_seq_reflexive a).
      apply nd_rule.
      apply sfc_flat with (r:=RBindingGroup _ _ _ _ _ _ ).
      auto.
      Defined.
*)
(*
    Definition systemfc_expansion n
      : @SequentExpansion _ (RuleSystemFCa n) _ (mkJudg Γ Δ) (ndr_systemfca n) (SystemFC_SC n) (systemfc_cutrule n).
    Check  (@Build_SequentExpansion).
apply (@Build_SequentExpansion _ _ _ _ (ndr_systemfca n)  _ _ (systemfc_left n) (systemfc_right n)).
      refine {| se_expand_left:=systemfc_left n
        ; se_expand_right:=systemfc_right n |}.

*)

    (* 5.1.2 *)
    Instance SystemFCa n Γ Δ : @ProgrammingLanguage _ _ (@mkUJudg Γ Δ) (OrgR true n Γ Δ) :=
    { pl_eqv                := OrgNDR true n Γ Δ
    ; pl_tsr                := _ (*@TreeStructuralRules Judg Rule T sequent*)
    ; pl_sc                 := _
    ; pl_subst              := _
    ; pl_sequent_join       := _
    }.
      apply Build_TreeStructuralRules; intros; unfold eqv; unfold hom; simpl.
      apply nd_rule; apply org_fc; apply nd_rule; simpl.  apply  (RURule _ _ _ _ (RCossa _ a b c)).
      apply nd_rule; apply org_fc; apply nd_rule; simpl;  apply  (RURule _ _ _ _ (RAssoc _ a b c)).
      apply nd_rule; apply org_fc; apply nd_rule; simpl;  apply  (RURule _ _ _ _ (RCanL  _ a    )).
      apply nd_rule; apply org_fc; apply nd_rule; simpl;  apply  (RURule _ _ _ _ (RCanR  _ a    )).
      apply nd_rule; apply org_fc; apply nd_rule; simpl;  apply  (RURule _ _ _ _ (RuCanL _ a    )).
      apply nd_rule; apply org_fc; apply nd_rule; simpl;  apply  (RURule _ _ _ _ (RuCanR _ a    )).
      Admitted.

    (* "flat" SystemFC: no brackets allowed *)
    Instance SystemFC Γ Δ : @ProgrammingLanguage _ _ (@mkUJudg Γ Δ) (OrgR true O Γ Δ) :=
    { pl_eqv                := OrgNDR true O Γ Δ
    ; pl_tsr                := _ (*@TreeStructuralRules Judg Rule T sequent*)
    ; pl_sc                 := _
    ; pl_subst              := _
    ; pl_sequent_join       := _
    }.
      Admitted.

    (* 5.1.3 *)
    Instance PCF n Γ Δ : @ProgrammingLanguage _ _ (@mkUJudg Γ Δ) (OrgR false n Γ Δ) :=
    { pl_eqv                := OrgNDR false n Γ Δ
    ; pl_tsr                := _ (*@TreeStructuralRules Judg Rule T sequent*)
    ; pl_sc                 := _
    ; pl_subst              := _
    ; pl_sequent_join       := _
    }.
      apply Build_TreeStructuralRules; intros; unfold eqv; unfold hom; simpl.
      apply nd_rule; apply org_pcf; simpl; exists (RCossa _ a b c); apply (PCF_RURule [_>>_>_|-_] [_>>_>_|-_]).
      apply nd_rule; apply org_pcf; simpl; exists (RAssoc _ a b c); apply (PCF_RURule [_>>_>_|-_] [_>>_>_|-_]).
      apply nd_rule; apply org_pcf; simpl; exists (RCanL  _ a    ); apply (PCF_RURule [_>>_>_|-_] [_>>_>_|-_]).
      apply nd_rule; apply org_pcf; simpl; exists (RCanR  _ a    ); apply (PCF_RURule [_>>_>_|-_] [_>>_>_|-_]).
      apply nd_rule; apply org_pcf; simpl; exists (RuCanL _ a    ); apply (PCF_RURule [_>>_>_|-_] [_>>_>_|-_]).
      apply nd_rule; apply org_pcf; simpl; exists (RuCanR _ a    ); apply (PCF_RURule [_>>_>_|-_] [_>>_>_|-_]).
    Admitted.

  (* gathers a tree of guest-language types into a single host-language types via the tensor *)
  Definition tensorizeType {Γ} (lt:Tree ??(LeveledHaskType Γ ★)) : HaskType Γ ★.
    admit.
    Defined.

  Definition mkGA {Γ} : HaskType Γ ★ -> HaskType Γ ★ -> HaskType Γ ★. 
    admit.
    Defined.

  Definition guestJudgmentAsGArrowType {Γ}{Δ} (lt:UJudg Γ Δ) : LeveledHaskType Γ ★ :=
    match lt with
      mkUJudg x y =>
      (mkGA (tensorizeType x) (tensorizeType y)) @@ nil
    end.

  Fixpoint obact n {Γ}{Δ}(X:Tree ??(UJudg Γ Δ)) : Tree ??(LeveledHaskType Γ ★) :=
    match n with
      | 0    => mapOptionTree guestJudgmentAsGArrowType X
      | S n' => let t := obact n' X
                in  [guestJudgmentAsGArrowType (Γ >> Δ > [] |- t )]
    end.

(*  Definition *)


  Definition magic {Γ}{Δ} h c n x :
Rule_PCF Γ Δ (mapOptionTree (@UJudg2judg Γ Δ) h) (mapOptionTree (@UJudg2judg Γ Δ) c) x
-> ND (OrgR true n Γ Δ) []
     [Γ >> Δ > mapOptionTree guestJudgmentAsGArrowType h
      |- mapOptionTree guestJudgmentAsGArrowType c].
  admit.
  Defined.

  (*
   * Here it is, what you've all been waiting for!  When reading this,
   * it might help to have the definition for "Inductive ND" (see
   * NaturalDeduction.v) handy as a cross-reference.
   *)
  Definition FlatteningFunctor_fmor {Γ}{Δ}
    : forall h c,
      (h~~{JudgmentsL _ _ (PCF 0 Γ Δ)}~~>c) ->
      ((obact 0 h)~~{TypesL _ _ (SystemFC Γ Δ)}~~>(obact 0 c)).
    unfold hom; unfold ob; unfold ehom; simpl; unfold mon_i; unfold obact; intros.

    induction X; simpl.

    (* the proof from no hypotheses of no conclusions (nd_id0) becomes REmptyGroup *)
    apply nd_rule; apply org_fc; simpl. apply nd_rule. apply REmptyGroup.

    (* the proof from hypothesis X of conclusion X (nd_id1) becomes RVar *)
    apply nd_rule; apply org_fc; simpl. apply nd_rule. destruct (guestJudgmentAsGArrowType h). apply RVar.

    (* the proof from hypothesis X of no conclusions (nd_weak) becomes RWeak;;REmptyGroup *)
    apply nd_rule; apply org_fc; simpl.
      eapply nd_comp; [ idtac | apply (nd_rule (RURule _ _ _ _ (RWeak _ _))) ].
      apply nd_rule. apply REmptyGroup.      

    (* the proof from hypothesis X of two identical conclusions X,,X (nd_copy) becomes RVar;;RBindingGroup;;RCont *)
    eapply nd_comp; [ idtac | eapply nd_rule; eapply org_fc; apply (nd_rule (RURule _ _ _ _ (RCont _ _))) ].
      eapply nd_comp; [ apply nd_llecnac | idtac ].
      set (nd_seq_reflexive(SequentCalculus:=@pl_sc  _ _ _ _ (SystemFC Γ Δ)) (mapOptionTree guestJudgmentAsGArrowType h)) as q.
      eapply nd_comp.
      eapply nd_prod.
      apply q.
      apply q.
      apply nd_rule; eapply org_fc.
      simpl.
      apply nd_rule.
      apply RBindingGroup.

    (* nd_prod becomes nd_llecnac;;nd_prod;;RBindingGroup *)
    eapply nd_comp.
      apply (nd_llecnac ;; nd_prod IHX1 IHX2).
      apply nd_rule; apply org_fc; simpl.
      eapply nd_rule. apply RBindingGroup.

    (* nd_comp becomes pl_subst (aka nd_cut) *)
    eapply nd_comp.
      apply (nd_llecnac ;; nd_prod IHX1 IHX2).
      clear IHX1 IHX2 X1 X2.
      apply (@nd_cut _ _ _ _ _ _ (@pl_subst _ _ _ _ (SystemFC Γ Δ))).

    (* nd_cancell becomes RVar;;RuCanL *)
    eapply nd_comp;
      [ idtac | eapply nd_rule; apply org_fc; simpl; apply nd_rule; apply (RURule _ _ _ _ (RuCanL _ _)) ].
      apply (nd_seq_reflexive(SequentCalculus:=@pl_sc  _ _ _ _ (SystemFC Γ Δ))).

    (* nd_cancelr becomes RVar;;RuCanR *)
    eapply nd_comp;
      [ idtac | eapply nd_rule; apply org_fc; simpl; apply nd_rule; apply (RURule _ _ _ _ (RuCanR _ _)) ].
      apply (nd_seq_reflexive(SequentCalculus:=@pl_sc  _ _ _ _ (SystemFC Γ Δ))).

    (* nd_llecnac becomes RVar;;RCanL *)
    eapply nd_comp;
      [ idtac | eapply nd_rule; apply org_fc; simpl; apply nd_rule; apply (RURule _ _ _ _ (RCanL _ _)) ].
      apply (nd_seq_reflexive(SequentCalculus:=@pl_sc  _ _ _ _ (SystemFC Γ Δ))).

    (* nd_rlecnac becomes RVar;;RCanR *)
    eapply nd_comp;
      [ idtac | eapply nd_rule; apply org_fc; simpl; apply nd_rule; apply (RURule _ _ _ _ (RCanR _ _)) ].
      apply (nd_seq_reflexive(SequentCalculus:=@pl_sc  _ _ _ _ (SystemFC Γ Δ))).

    (* nd_assoc becomes RVar;;RAssoc *)
    eapply nd_comp;
      [ idtac | eapply nd_rule; apply org_fc; simpl; apply nd_rule; apply (RURule _ _ _ _ (RAssoc _ _ _ _)) ].
      apply (nd_seq_reflexive(SequentCalculus:=@pl_sc  _ _ _ _ (SystemFC Γ Δ))).

    (* nd_coss becomes RVar;;RCossa *)
    eapply nd_comp;
      [ idtac | eapply nd_rule; apply org_fc; simpl; apply nd_rule; apply (RURule _ _ _ _ (RCossa _ _ _ _)) ].
      apply (nd_seq_reflexive(SequentCalculus:=@pl_sc  _ _ _ _ (SystemFC Γ Δ))).

    (* now, the interesting stuff: the inference rules of Judgments(PCF) become GArrow-parameterized terms *)
      refine (match r as R in OrgR B N G D H C return
                match N with
                  | S _ => True
                  | O   => if B then True
                           else ND (OrgR true 0 G D)
                                  []
                                  [G >> D > mapOptionTree guestJudgmentAsGArrowType H |- mapOptionTree guestJudgmentAsGArrowType C]
                end with
                | org_pcf  n Γ Δ h c b r => _
                | org_fc   n Γ Δ h c r => _
                | org_nest n Γ Δ h c b v q => _
              end); destruct n; try destruct b; try apply I.
      destruct r0.

      clear r h c Γ Δ.
      rename r0 into r; rename h0 into h; rename c0 into c; rename Γ0 into Γ; rename Δ0 into Δ.

      refine (match r as R in Rule_PCF G D H C with
                | PCF_RURule           h c r            => let case_RURule := tt in _
                | PCF_RLit             Σ τ              => let case_RLit := tt in _
                | PCF_RNote            Σ τ l n          => let case_RNote := tt in _
                | PCF_RVar             σ               l=> let case_RVar := tt in _
                | PCF_RLam             Σ tx te    q     => let case_RLam := tt in _
                | PCF_RApp             Σ tx te   p     l=> let case_RApp := tt in _
                | PCF_RLet             Σ σ₁ σ₂   p     l=> let case_RLet := tt in _
                | PCF_RBindingGroup    q a b c d e      => let case_RBindingGroup := tt in _
                | PCF_RCase            T κlen κ θ l x   => let case_RCase := tt in _
                | PCF_REmptyGroup      q a              => let case_REmptyGroup := tt in _
                | PCF_RLetRec          Σ₁ τ₁ τ₂ lev     => let case_RLetRec := tt in _
              end).
      rename Γ

      apply (magic _ _ _ _ r0).
      Defined.

  Instance FlatteningFunctor {n}{Γ}{Δ} : Functor (JudgmentsL _ _ (PCF n Γ Δ)) (TypesL _ _ (SystemFCa n Γ Δ)) obact :=
    { fmor := FlatteningFunctor_fmor }.
    unfold hom; unfold ob; unfold ehom; intros; simpl.


  Definition productifyType {Γ} (lt:Tree ??(LeveledHaskType Γ ★)) : LeveledHaskType Γ ★.
    admit.
    Defined.

  Definition exponent {Γ} : LeveledHaskType Γ ★ -> LeveledHaskType Γ ★ -> LeveledHaskType Γ ★. 
    admit.
    Defined.

  Definition brakify {Γ}(Σ τ:Tree ??(LeveledHaskType Γ ★))  := exponent (productifyType Σ) (productifyType τ).

  Definition brakifyJudg (j:Judg) : Judg :=
    match j with
      Γ > Δ > Σ |- τ =>
        Γ > Δ > [] |- [brakify Σ τ]
    end.

  Definition brakifyUJudg (j:Judg) : Judg :=
    match j with
      Γ > Δ > Σ |- τ =>
        Γ > Δ > [] |- [brakify Σ τ]
    end.
  *)

  End RuleSystemFC.

  Context (ndr_pcf      :forall n Γ Δ, @ND_Relation _ (@RulePCF Γ Δ n)).


  Instance PCF n Γ Δ : @ProgrammingLanguage _ _ (mkJudg Γ Δ) (@RulePCF Γ Δ n) :=
  { pl_eqv                := _
  ; pl_tsr                := _ (*@TreeStructuralRules Judg Rule T sequent*)
  ; pl_sc                 := _ (*@SequentCalculus Judg Rule _ sequent*)
  ; pl_subst              := _ (*@CutRule Judg Rule _ sequent pl_eqv pl_sc*)
  ; pl_sequent_join       := _ (*@SequentExpansion Judg Rule T sequent pl_eqv pl_sc pl_subst*)
  }.
  Admitted.

  Inductive RuleX : nat -> Tree ??Judg -> Tree ??Judg -> Type :=
  | x_flat : forall n     h c   (r:Rule h c), Rule_Flat r -> RuleX    n  h c
  | x_nest : forall n Γ Δ h c,  ND (@RulePCF Γ Δ n) h c   ->
    RuleX (S n) (mapOptionTree brakifyJudg h) (mapOptionTree brakifyJudg c).

  Section X.

    Context (n:nat).
    Context (ndr:@ND_Relation _ (RuleX (S n))).

    Definition SystemFCa' := Judgments_Category ndr.

    Definition ReificationFunctor_fmor Γ Δ
      : forall h c,
        (h~~{JudgmentsL _ _ (PCF n Γ Δ)}~~>c) ->
        ((mapOptionTree brakifyJudg h)~~{SystemFCa'}~~>(mapOptionTree brakifyJudg c)).
      unfold hom; unfold ob; simpl.
      intros.
      apply nd_rule.
      eapply x_nest.
      apply X.
      Defined.

    Definition ReificationFunctor Γ Δ : Functor (JudgmentsL _ _ (PCF n Γ Δ)) SystemFCa' (mapOptionTree brakifyJudg).
      refine {| fmor := ReificationFunctor_fmor Γ Δ |}; unfold hom; unfold ob; simpl ; intros.
      unfold ReificationFunctor_fmor; simpl.
      admit.
      unfold ReificationFunctor_fmor; simpl.
      admit.
      unfold ReificationFunctor_fmor; simpl.
      admit.
      Defined.

    Definition FlatteningFunctor Γ Δ : Functor (JudgmentsL _ _ (PCF n Γ Δ)) SystemFCa' (mapOptionTree brakify).
      refine {| fmor := ReificationFunctor_fmor Γ Δ |}; unfold hom; unfold ob; simpl ; intros.
      unfold ReificationFunctor_fmor; simpl.
      admit.
      unfold ReificationFunctor_fmor; simpl.
      admit.
      unfold ReificationFunctor_fmor; simpl.
      admit.
      Defined.

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
    (*  ... and the retraction exists *)
    Defined.

  (* Any particular proof in HaskProof is only finitely large, so it uses only finitely many levels of nesting, so
   * it falls within (SystemFCa n) for some n.  This function calculates that "n" and performs the translation *)
  (*
  Definition HaskProof_to_SystemFCa :
    forall h c (pf:ND Rule h c),
      { n:nat & h ~~{JudgmentsL (SystemFCa_SMME n)}~~> c }.
      *)

  (* for every n we have a functor from the category of (n+1)-bounded proofs to the category of n-bounded proofs *)


  Definition makeTree : Tree ??(LeveledHaskType Γ ★) -> HaskType Γ ★.
    admit.
    Defined.

  Definition flattenType n (j:JudgmentsN n) : TypesN n.
    unfold eob_eob.
    unfold ob in j.
    refine (mapOptionTree _ j).
    clear j; intro j.
    destruct j as [ Γ' Δ' Σ τ ].
    assert (Γ'=Γ). admit.
    rewrite H in *.
    clear H Γ'.
    refine (_ @@ nil).
    refine (HaskBrak _ ( (makeTree Σ) ---> (makeTree τ) )); intros.
    admit.
    Defined.

  Definition FlattenFunctor_fmor n :
    forall h c,
      (h~~{JudgmentsN n}~~>c) -> 
      ((flattenType n h)~~{TypesN n}~~>(flattenType n c)).
    intros.
    unfold hom in *; simpl.
    unfold mon_i.
    unfold ehom.
    unfold TypesNmor.

    admit.
    Defined.

  Definition FlattenFunctor n : Functor (JudgmentsN n) (TypesN n) (flattenType n).
    refine {| fmor := FlattenFunctor_fmor n |}; intros.
    admit.
    admit.
    admit.
    Defined.
    
  End RulePCF.
  Implicit Arguments Rule_PCF [ [h] [c] ].
  Implicit Arguments BoundedRule [ ].

*)
(*
  Definition code2garrow0 {Γ}(ec t1 t2:RawHaskType Γ ★) : RawHaskType Γ ★.
    admit.
    Defined.
  Definition code2garrow Γ (ec t:RawHaskType Γ ★) :=
      match t with
(*        | TApp ★ ★ (TApp _ ★ TArrow tx) t' => code2garrow0 ec tx       t'*)
        |                               _  => code2garrow0 ec unitType t
      end.
  Opaque code2garrow.
  Fixpoint typeMap {TV}{κ}(ty:@RawHaskType TV κ) : @RawHaskType TV κ :=
      match ty as TY in RawHaskType _ K return RawHaskType TV K with
        | TCode ec t        => code2garrow _ ec t
        | TApp _ _ t1 t2    => TApp (typeMap t1) (typeMap t2)
        | TAll _ f          => TAll _ (fun tv => typeMap (f tv))
        | TCoerc _ t1 t2 t3 => TCoerc (typeMap t1) (typeMap t2) (typeMap t3)
        | TVar   _ v        => TVar v
        | TArrow            => TArrow
        | TCon  tc          => TCon tc 
        | TyFunApp  tf rhtl => (* FIXME *) TyFunApp tf rhtl
      end.
          
  Definition typeMapL {Γ}(lht:LeveledHaskType Γ ★) : LeveledHaskType Γ ★  :=
    match lht with
(*      | t @@ nil       => (fun TV ite => typeMap (t TV ite)) @@ lev*)
      | t @@ lev => (fun TV ite => typeMap (t TV ite)) @@ lev
    end.

  Definition coMap {Γ}(ck:HaskCoercionKind Γ) := 
    fun TV ite => match ck TV ite with 
      | mkRawCoercionKind _ t1 t2 => mkRawCoercionKind _ (typeMap t1) (typeMap t2)
      end.

  Definition flattenCoercion {Γ}{Δ}{ck}(hk:HaskCoercion Γ Δ ck) : HaskCoercion Γ (map coMap Δ) (coMap ck).
    admit.
    Defined.

  Lemma update_typeMap Γ (lev:HaskLevel Γ) ξ v t
    : (typeMap ○ (update_ξ            ξ  lev ((⟨v, t ⟩)          :: nil)))
    = (           update_ξ (typeMap ○ ξ) lev ((⟨v, typeMap_ t ⟩) :: nil)).
    admit.
    Qed.

  Lemma foo κ Γ σ τ : typeMap_ (substT σ τ) = substT(Γ:=Γ)(κ₁:=κ) (fun TV ite => typeMap ○ σ TV ite) τ.
    admit.
    Qed.

  Lemma lit_lemma lit Γ : typeMap_ (literalType lit) = literalType(Γ:=Γ) lit.
    admit.
    Qed.
*)
(*
  Definition flatten : forall h c, Rule h c -> @ND Judg Rule (mapOptionTree flattenJudgment h) (mapOptionTree flattenJudgment c).
    intros h c r.
    refine (match r as R in Rule H C return ND Rule (mapOptionTree flattenJudgment H) (mapOptionTree flattenJudgment C) with
      | RURule  a b c d e             => let case_RURule := tt        in _
      | RNote   Γ Δ Σ τ l n           => let case_RNote := tt         in _
      | RLit    Γ Δ l     _           => let case_RLit := tt          in _
      | RVar    Γ Δ σ         p       => let case_RVar := tt          in _
      | RGlobal Γ Δ σ l wev           => let case_RGlobal := tt       in _
      | RLam    Γ Δ Σ tx te     x     => let case_RLam := tt          in _
      | RCast   Γ Δ Σ σ τ γ     x     => let case_RCast := tt         in _
      | RAbsT   Γ Δ Σ κ σ a           => let case_RAbsT := tt         in _
      | RAppT   Γ Δ Σ κ σ τ     y     => let case_RAppT := tt         in _
      | RAppCo  Γ Δ Σ κ σ₁ σ₂ γ σ l   => let case_RAppCo := tt        in _
      | RAbsCo  Γ Δ Σ κ σ  σ₁ σ₂  y   => let case_RAbsCo := tt        in _
      | RApp    Γ Δ Σ₁ Σ₂ tx te p     => let case_RApp := tt          in _
      | RLet    Γ Δ Σ₁ Σ₂ σ₁ σ₂ p     => let case_RLet := tt          in _
      | RBindingGroup Γ p lri m x q   => let case_RBindingGroup := tt in _
      | REmptyGroup _ _               => let case_REmptyGroup := tt   in _
      | RBrak   Σ a b c n m           => let case_RBrak := tt         in _
      | REsc    Σ a b c n m           => let case_REsc := tt          in _
      | RCase   Γ Δ lev tc Σ avars tbranches alts => let case_RCase := tt         in _
      | RLetRec Γ Δ lri x y t         => let case_RLetRec := tt       in _
      end).

      destruct case_RURule.
        admit.

      destruct case_RBrak.
        simpl.
        admit.

      destruct case_REsc.
        simpl.
        admit.

      destruct case_RNote.
        eapply nd_rule.  simpl.  apply RNote; auto.

      destruct case_RLit.
        simpl.

      set (@RNote Γ Δ Σ τ l) as q.
    Defined.

  Definition flatten' {h}{c} (pf:ND Rule h c) := nd_map' flattenJudgment flatten pf.


    @ND Judgment1 Rule1 (mapOptionTree f h) (mapOptionTree f c).

  refine (fix flatten : forall Γ Δ Σ τ
    (pf:SCND Rule [] [Γ > Δ >                       Σ |-                       τ ]) :
    SCND Rule [] [Γ > Δ > mapOptionTree typeMap Σ |- mapOptionTree typeMap τ ] :=
    match pf as SCND _ _ 
    | scnd_comp   : forall ht ct c , SCND ht ct -> Rule ct [c] -> SCND ht [c]
  | scnd_weak   : forall c       , SCND c  []
  | scnd_leaf   : forall ht c    , SCND ht [c]  -> SCND ht [c]
  | scnd_branch : forall ht c1 c2, SCND ht c1 -> SCND ht c2 -> SCND ht (c1,,c2)
  Expr Γ Δ ξ τ -> Expr Γ (map coMap Δ) (typeMap ○ ξ) (typeMap τ).
*)

(*
  Lemma all_lemma Γ κ σ l : 
(@typeMap (κ :: Γ)
           (@HaskTApp (κ :: Γ) κ (@weakF Γ κ ★ σ) (@FreshHaskTyVar Γ κ) @@ 
            @weakL Γ κ l)) = (@typeMap Γ (@HaskTAll Γ κ σ @@  l)).
*)

(*    
  Definition flatten : forall Γ Δ ξ τ,  Expr Γ Δ ξ τ -> Expr Γ (map coMap Δ) (typeMap ○ ξ) (typeMap τ).
  refine (fix flatten Γ' Δ' ξ' τ' (exp:Expr Γ' Δ' ξ' τ') : Expr Γ' (map coMap Δ') (typeMap ○ ξ') (typeMap τ') :=
    match exp as E in Expr G D X T return Expr G (map coMap D) (typeMap ○ X) (typeMap T) with
    | EGlobal  Γ Δ ξ t wev                          => EGlobal _ _ _ _  wev
    | EVar     Γ Δ ξ ev                             => EVar    _ _ _    ev
    | ELit     Γ Δ ξ lit lev                        => let case_ELit    := tt in _
    | EApp     Γ Δ ξ t1 t2 lev e1 e2                => EApp _ _ _ _ _ _ (flatten _ _ _ _ e1) (flatten _ _ _ _ e2)
    | ELam     Γ Δ ξ t1 t2 lev v    e               => let case_ELam := tt in _
    | ELet     Γ Δ ξ tv t  l ev elet ebody          => let case_ELet    := tt in _
    | ELetRec  Γ Δ ξ lev t tree branches ebody      => let case_ELetRec := tt in _
    | ECast    Γ Δ ξ t1 t2 γ lev e                  => let case_ECast   := tt in _
    | ENote    Γ Δ ξ t n e                          => ENote _ _ _ _ n (flatten _ _ _ _ e)
    | ETyLam   Γ Δ ξ κ σ l e                        => let case_ETyLam  := tt in _
    | ECoLam   Γ Δ κ σ σ₁ σ₂ ξ l             e      => let case_ECoLam  := tt in _
    | ECoApp   Γ Δ κ σ₁ σ₂ γ σ ξ l e                => let case_ECoApp  := tt in _
    | ETyApp   Γ Δ κ σ τ ξ  l    e                  => let case_ETyApp  := tt in _
    | ECase    Γ Δ ξ l tc tbranches atypes e alts'  => let case_ECase   := tt in _

    | EEsc     Γ Δ ξ ec t lev e                     => let case_EEsc    := tt in _
    | EBrak    Γ Δ ξ ec t lev e                     => let case_EBrak   := tt in _
    end); clear exp ξ' τ' Γ' Δ'.

  destruct case_ELit.
    simpl.
    rewrite lit_lemma.
    apply ELit.

  destruct case_ELam.
    set (flatten _ _ _ _ e) as q.
    rewrite update_typeMap in q.
    apply (@ELam _ _ _ _ _ _ _ _ v q).

  destruct case_ELet.
    set (flatten _ _ _ _ ebody) as ebody'.
    set (flatten _ _ _ _ elet)  as elet'.
    rewrite update_typeMap in ebody'.
    apply (@ELet _ _ _ _ _ _ _ _ _ elet' ebody').

  destruct case_EEsc.
    admit.
  destruct case_EBrak.
    admit.

  destruct case_ECast.
    apply flatten in e.
    eapply ECast in e.
    apply e.
    apply flattenCoercion in γ.
    apply γ.

  destruct case_ETyApp.
    apply flatten in e.
    simpl in e.
    unfold HaskTAll in e.
    unfold typeMap_ in e.
    simpl in e.
    eapply ETyApp in e.
    rewrite <- foo in e.
    apply e.

  destruct case_ECoLam.
    apply flatten in e.
    simpl in e.
    set (@ECoLam _ _ _ _ _ _ _ _ _ _ e) as x.
    simpl in x.
    simpl.
    unfold typeMap_.
    simpl.
    apply x.

  destruct case_ECoApp.
    simpl.
    apply flatten in e.
    eapply ECoApp.
    unfold mkHaskCoercionKind in *.
    simpl in γ.
    apply flattenCoercion in γ.
    unfold coMap in γ at 2.
    apply γ.
    apply e.
   
  destruct case_ETyLam.
    apply flatten in e.
    set (@ETyLam Unique _ Γ (map coMap Δ) (typeMap ○ ξ) κ (fun ite x => typeMap (σ x ite))) as e'.
    unfold HaskTAll in *.
    unfold typeMap_ in *.
    rewrite <- foo in e'.
    unfold typeMap in e'.
    simpl in e'.
    apply ETyLam.

Set Printing Implicit.
idtac.
idtac.


    admit.
   
  destruct case_ECase.
    admit.

  destruct case_ELetRec.
    admit.
    Defined.

  (* This proof will work for any dynamic semantics you like, so
   * long as those semantics are an ND_Relation (associativity,
   * neutrality, etc) *)
  Context (dynamic_semantics   : @ND_Relation _ Rule).

  Section SystemFC_Category.

    Context {Γ:TypeEnv}
            {Δ:CoercionEnv Γ}.

    Definition Context := Tree ??(LeveledHaskType Γ ★).

    Notation "a |= b" := (Γ >> Δ > a |- b).

    (*
       SystemFCa
       PCF
       SystemFCa_two_level
       SystemFCa_initial_GArrow
     *)

    Context (nd_eqv:@ND_Relation _ (@URule Γ Δ)).
    Check (@ProgrammingLanguage).
    Context (PL:@ProgrammingLanguage (LeveledHaskType Γ ★)
      (fun x y => match x with x1|=x2 => match y with y1|=y2 => @URule Γ Δ)).
    Definition JudgmentsFC := @Judgments_Category_CartesianCat _ (@URule Γ Δ) nd_eqv.
    Definition TypesFC     := @TypesL                          _ (@URule Γ Δ) nd_eqv.

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
        | judgmentsAtLevel_leaf   : forall c1 c2, ContextAtLevel c1   -> ContextAtLevel c2   -> JudgmentsAtLevel [c1 |= c2]
        | judgmentsAtLevel_branch : forall j1 j2, JudgmentsAtLevel j1 -> JudgmentsAtLevel j2 -> JudgmentsAtLevel (j1,,j2).
  
      Definition JudgmentsFCAtLevel := FullSubcategory JudgmentsFC JudgmentsAtLevel.
      Definition TypesFCAtLevel     := FullSubcategory TypesFC     ContextAtLevel.
    End SingleLevel.

  End SystemFC_Category.

  Implicit Arguments TypesFC [ ].
    
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
*)
End HaskProofCategory.
