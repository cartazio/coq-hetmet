(*********************************************************************************************************************************)
(* HaskProofToStrong: convert HaskProof to HaskStrong                                                                            *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import NaturalDeduction.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Specif.
Require Import HaskKinds.
Require Import HaskStrongTypes.
Require Import HaskStrong.
Require Import HaskProof.

Section HaskProofToStrong.

  Context {VV:Type} {eqdec_vv:EqDecidable VV}.

  Definition Exprs Γ Δ ξ τ :=
    ITree _ (fun τ => Expr Γ Δ ξ τ) τ.

  Definition judg2exprType (j:Judg) : Type :=
    match j with
      (Γ > Δ > Σ |- τ) => forall (ξ:VV -> LeveledHaskType Γ ★ ) vars, Σ=mapOptionTree ξ vars -> Exprs Γ Δ ξ τ
      end.

  Definition judges2exprType (j:Tree ??Judg) : Type :=
    ITree _ judg2exprType j.

  Definition urule2expr Γ Δ : forall h j (r:@URule Γ Δ h j),
    judges2exprType (mapOptionTree UJudg2judg h) -> judges2exprType (mapOptionTree UJudg2judg j).

    intros h j r.

      refine (match r as R in URule H C
                  return judges2exprType (mapOptionTree UJudg2judg H) -> judges2exprType (mapOptionTree UJudg2judg C) with
      | RLeft   h c ctx r => let case_RLeft := tt in _
      | RRight  h c ctx r => let case_RRight := tt in _
      | RCanL   t a       => let case_RCanL := tt in _
      | RCanR   t a       => let case_RCanR := tt in _
      | RuCanL  t a       => let case_RuCanL := tt in _
      | RuCanR  t a       => let case_RuCanR := tt in _
      | RAssoc  t a b c   => let case_RAssoc := tt in _
      | RCossa  t a b c   => let case_RCossa := tt in _
      | RExch   t a b     => let case_RExch := tt in _
      | RWeak   t a       => let case_RWeak := tt in _
      | RCont   t a       => let case_RCont := tt in _
              end   ); intros.

      destruct case_RCanL.
        apply ILeaf; simpl; intros.
        inversion X.
        simpl in X0.
        apply (X0 ξ ([],,vars)).
        simpl; rewrite <- H; auto.

      destruct case_RCanR.
        apply ILeaf; simpl; intros.
        inversion X.
        simpl in X0.
        apply (X0 ξ (vars,,[])).
        simpl; rewrite <- H; auto.

      destruct case_RuCanL.
        apply ILeaf; simpl; intros.
        destruct vars; try destruct o; inversion H.
        inversion X.
        simpl in X0.
        apply (X0 ξ vars2); auto.

      destruct case_RuCanR.
        apply ILeaf; simpl; intros.
        destruct vars; try destruct o; inversion H.
        inversion X.
        simpl in X0.
        apply (X0 ξ vars1); auto.

      destruct case_RAssoc.
        apply ILeaf; simpl; intros.
        inversion X.
        simpl in X0.
        destruct vars; try destruct o; inversion H.
        destruct vars1; try destruct o; inversion H.
        apply (X0 ξ (vars1_1,,(vars1_2,,vars2))).
        subst; auto.

      destruct case_RCossa.
        apply ILeaf; simpl; intros.
        inversion X.
        simpl in X0.
        destruct vars; try destruct o; inversion H.
        destruct vars2; try destruct o; inversion H.
        apply (X0 ξ ((vars1,,vars2_1),,vars2_2)).
        subst; auto.

      destruct case_RLeft.
        (* this will require recursion *)
        admit.
        
      destruct case_RRight.
        (* this will require recursion *)
        admit.

      destruct case_RExch.
        apply ILeaf; simpl; intros.
        inversion X.
        simpl in X0.
        destruct vars; try destruct o; inversion H.
        apply (X0 ξ (vars2,,vars1)).
        inversion H; subst; auto.
        
      destruct case_RWeak.
        apply ILeaf; simpl; intros.
        inversion X.
        simpl in X0.
        apply (X0 ξ []).
        auto.
        
      destruct case_RCont.
        apply ILeaf; simpl; intros.
        inversion X.
        simpl in X0.
        apply (X0 ξ (vars,,vars)).
        simpl.
        rewrite <- H.
        auto.
        Defined.

  Definition rule2expr : forall h j (r:Rule h j), judges2exprType h -> judges2exprType j.

    intros h j r.

      refine (match r as R in Rule H C return judges2exprType H -> judges2exprType C with
      | RURule a b c d e    => let case_RURule := tt in _
      | RNote   Γ Δ Σ τ l n         => let case_RNote := tt in _
      | RLit    Γ Δ l     _    => let case_RLit := tt in _
      | RVar    Γ Δ σ         p => let case_RVar := tt in _
      | RGlobal Γ Δ σ l wev     => let case_RGlobal := tt in _
      | RLam    Γ Δ Σ tx te     x => let case_RLam := tt in _
      | RCast   Γ Δ Σ σ τ γ     x => let case_RCast := tt in _
      | RAbsT   Γ Δ Σ κ σ a    => let case_RAbsT := tt in _
      | RAppT   Γ Δ Σ κ σ τ     y => let case_RAppT := tt in _
      | RAppCo  Γ Δ Σ κ σ₁ σ₂ γ σ l => let case_RAppCo := tt in _
      | RAbsCo  Γ Δ Σ κ σ  σ₁ σ₂  y => let case_RAbsCo := tt in _
      | RApp    Γ Δ Σ₁ Σ₂ tx te p => let case_RApp := tt in _
      | RLet    Γ Δ Σ₁ Σ₂ σ₁ σ₂ p => let case_RLet := tt in _
      | RLetRec Γ p lri x y => let case_RLetRec := tt in _
      | RBindingGroup Γ p lri m x q => let case_RBindingGroup := tt in _
      | REmptyGroup _ _ => let case_REmptyGroup := tt in _
      | RCase   Σ Γ T κlen κ θ ldcd τ  => let case_RCase := tt in _
      | RBrak   Σ a b c n m => let case_RBrak := tt in _
      | REsc    Σ a b c n m => let case_REsc := tt in _
      end); intros.

  destruct case_RURule.
    eapply urule2expr.
    apply e.
    apply X.

  destruct case_RBrak.
    apply ILeaf; simpl; intros; apply ILeaf.
    apply EBrak.
    inversion X.
    set (X0 ξ vars H) as X'.
    inversion X'.
    apply X1.

  destruct case_REsc.
    apply ILeaf; simpl; intros; apply ILeaf.
    apply EEsc.
    inversion X.
    set (X0 ξ vars H) as X'.
    inversion X'.
    apply X1.

  destruct case_RNote.
    apply ILeaf; simpl; intros; apply ILeaf.
    inversion X.
    apply ENote.
    apply n.
    simpl in X0.
    set (X0 ξ vars H) as x1.
    inversion x1.
    apply X1.

  destruct case_RLit.
    apply ILeaf; simpl; intros; apply ILeaf.
    apply ELit.

  destruct case_RVar.
    apply ILeaf; simpl; intros; apply ILeaf.
    destruct vars; simpl in H; inversion H; destruct o. inversion H1. rewrite H2.
    apply EVar.
    inversion H.

  destruct case_RGlobal.
    apply ILeaf; simpl; intros; apply ILeaf.
    apply EGlobal.
    apply wev.

  destruct case_RLam.
    apply ILeaf; simpl; intros; apply ILeaf.
    (* need a fresh variable here *)
    admit.

  destruct case_RCast.
    apply ILeaf; simpl; intros; apply ILeaf.
    eapply ECast.
    apply x.
    inversion X.
    simpl in X0.
    set (X0 ξ vars H) as q.
    inversion q.
    apply X1.

  destruct case_RBindingGroup.
    apply ILeaf; simpl; intros.
    inversion X.
    inversion X0.
    inversion X1.
    destruct vars; inversion H.
    destruct o; inversion H5.
    set (X2 _ _ H5) as q1.
    set (X3 _ _ H6) as q2.
    apply IBranch; auto.

  destruct case_RApp.    
    apply ILeaf; simpl; intros; apply ILeaf.
    inversion X.
    inversion X0.
    inversion X1.
    destruct vars; try destruct o; inversion H.
    set (X2 _ _ H5) as q1.
    set (X3 _ _ H6) as q2.
    eapply EApp.
      inversion q1.
      apply X4.
      inversion q2.
      apply X4.

  destruct case_RLet.
    apply ILeaf; simpl; intros; apply ILeaf.
    (* FIXME: need a var here, and other work *)
    admit.

  destruct case_REmptyGroup.
    apply ILeaf; simpl; intros.
    apply INone.

  destruct case_RAppT.
    apply ILeaf; simpl; intros; apply ILeaf.
    apply ETyApp.
    inversion X.
    set (X0 _ _ H) as q.
    inversion q.
    apply X1.

  destruct case_RAbsT.
    apply ILeaf; simpl; intros; apply ILeaf.
    apply ETyLam.
    inversion X.
    simpl in *.
    set (X0 (weakLT ○ ξ) vars) as q.
    rewrite mapOptionTree_compose in q.
    rewrite <- H in q.
    set (q (refl_equal _)) as q'.
    inversion q'.
    apply X1.

  destruct case_RAppCo.
    apply ILeaf; simpl; intros; apply ILeaf.
    eapply ECoApp.
    apply γ.
    inversion X.
    set (X0 _ _ H) as q.
    inversion q.
    apply X1.

  destruct case_RAbsCo.
    apply ILeaf; simpl; intros; apply ILeaf.
    eapply ECoLam.
    inversion X.
    set (X0 _ _ H) as q.
    inversion q; auto.

  destruct case_RLetRec.
    admit.

  destruct case_RCase.
    admit.

      Defined.

  Definition closed2expr : forall c (pn:@ClosedND _ Rule c), ITree _ judg2exprType c.
    refine ((
      fix closed2expr' j (pn:@ClosedND _ Rule j) {struct pn} : ITree _ judg2exprType j :=
      match pn in @ClosedND _ _ J return ITree _ judg2exprType J with
      | cnd_weak             => let case_nil    := tt in _
      | cnd_rule h c cnd' r  => let case_rule   := tt in (fun rest => _) (closed2expr' _ cnd')
      | cnd_branch _ _ c1 c2 => let case_branch := tt in (fun rest1 rest2 => _) (closed2expr' _ c1) (closed2expr' _ c2)
      end)); clear closed2expr'; intros; subst.

      destruct case_nil.
        apply INone.

      destruct case_rule.
        eapply rule2expr.
        apply r.
        apply rest.

      destruct case_branch.
        apply IBranch.
        apply rest1.
        apply rest2.
        Defined.

  Definition proof2expr Γ Δ τ Σ : ND Rule [] [Γ > Δ > Σ |- [τ]] -> { ξ:VV -> LeveledHaskType Γ ★ & Expr Γ Δ ξ τ }.
    intro pf.
    set (closedFromSCND _ _ (mkSCND systemfc_all_rules_one_conclusion _ _ _ pf (scnd_weak [])) cnd_weak) as cnd.
    apply closed2expr in cnd.
    inversion cnd; subst.
    simpl in X.
    clear cnd pf.
    destruct X.
    exists x.
    inversion e.
    subst.
    apply X.
    Defined.

End HaskProofToStrong.
