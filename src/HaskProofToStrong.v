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

  Context
    {VV:Type}
    {eqdec_vv:EqDecidable VV}
    {fresh: forall (l:list VV), { lf:VV & distinct (lf::l) }}.

  Definition Exprs (Γ:TypeEnv)(Δ:CoercionEnv Γ)(ξ:VV -> LeveledHaskType Γ ★)(τ:Tree ??(LeveledHaskType Γ ★)) :=
    ITree _ (fun τ => Expr Γ Δ ξ τ) τ.

  Definition judg2exprType (j:Judg) : Type :=
    match j with
      (Γ > Δ > Σ |- τ) => { ξ:VV -> LeveledHaskType Γ ★ & Exprs Γ Δ ξ τ }
      end.

  (* reminder: need to pass around uniq-supplies *)
  Definition rule2expr
    : forall h j
      (r:Rule h [j]),
      ITree _ judg2exprType h ->
      judg2exprType j.
  
      intros.
      destruct j.
      refine (match r as R in Rule H C return C=[Γ > Δ > t |- t0] -> _ with
      | RURule a b c d e    => let case_RURule := tt in _
      | RNote   x n z        => let case_RNote := tt in _
      | RLit    Γ Δ l     _    => let case_RLit := tt in _
      | RVar    Γ Δ σ         p => let case_RVar := tt in _
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
              end (refl_equal _)  ); intros.

    destruct case_RURule.
      destruct d; [ destruct o | idtac ]; inversion H; subst.
      clear H.
      destruct u.
      refine (match e as R in URule H C return C=[a >> b > t1 |- t2] -> _ with
      | RLeft   h c ctx r   => let case_RLeft := tt in _
      | RRight  h c ctx r   => let case_RRight := tt in _
      | RCanL   t a       => let case_RCanL := tt in _
      | RCanR   t a       => let case_RCanR := tt in _
      | RuCanL  t a       => let case_RuCanL := tt in _
      | RuCanR  t a       => let case_RuCanR := tt in _
      | RAssoc  t a b c   => let case_RAssoc := tt in _
      | RCossa  t a b c   => let case_RCossa := tt in _
      | RExch   t a b     => let case_RExch := tt in _
      | RWeak   t a       => let case_RWeak := tt in _
      | RCont   t a       => let case_RCont := tt in _
              end (refl_equal _)  ); intros.

      destruct case_RCanL. admit.
      destruct case_RCanR. admit.
      destruct case_RuCanL. admit.
      destruct case_RuCanR. admit.
      destruct case_RAssoc. admit.
      destruct case_RCossa. admit.
      destruct case_RLeft. admit.
      destruct case_RRight. admit.
      destruct case_RExch. admit.
      destruct case_RWeak. admit.
      destruct case_RCont. admit.
      destruct case_RBrak. admit.
      destruct case_REsc. admit.
      destruct case_RNote. admit.
      destruct case_RLit. admit.
      destruct case_RVar. admit.
      destruct case_RLam. admit.
      destruct case_RCast. admit.
      destruct case_RBindingGroup. admit.
      destruct case_RApp. admit.
      destruct case_RLet. admit.
      destruct case_REmptyGroup. admit.
      destruct case_RAppT. admit.
      destruct case_RAbsT. admit.
      destruct case_RAppCo. admit.
      destruct case_RAbsCo. admit.
      destruct case_RLetRec. admit.
      destruct case_RCase. admit.
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
        set (@rule2expr h) as q.
        destruct c.
        destruct o.
        apply ILeaf.
        eapply rule2expr.
        apply r.
        apply rest.

        apply no_rules_with_empty_conclusion in r.
        inversion r.
        auto.

        simpl.
        apply systemfc_all_rules_one_conclusion in r.
        inversion r.

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
