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

  Context {VV:Type} {eqdec_vv:EqDecidable VV} {freshM:FreshMonad VV}.

  Definition fresh := FMT_fresh freshM.
  Definition FreshM := FMT freshM.
  Definition FreshMon := FMT_Monad freshM.
  Existing Instance FreshMon.

  Definition ExprVarResolver Γ := VV -> LeveledHaskType Γ ★.

  Definition ujudg2exprType {Γ}{Δ}(ξ:ExprVarResolver Γ)(j:UJudg Γ Δ) : Type :=
    match j with
      mkUJudg Σ τ => forall vars, Σ = mapOptionTree ξ vars ->
        FreshM (ITree _ (fun t => Expr Γ Δ ξ t) τ)
      end.

  Definition judg2exprType (j:Judg) : Type :=
    match j with
      (Γ > Δ > Σ |- τ) => forall (ξ:ExprVarResolver Γ) vars, Σ = mapOptionTree ξ vars ->
        FreshM (ITree _ (fun t => Expr Γ Δ ξ t) τ)
      end.

  Definition justOne Γ Δ ξ τ : ITree _ (fun t => Expr Γ Δ ξ t) [τ] -> Expr Γ Δ ξ τ.
    intros.
    inversion X; auto.
    Defined.

  Definition ileaf `(it:ITree X F [t]) : F t.
    inversion it.
    apply X0.
    Defined.

  Lemma update_branches : forall Γ (ξ:VV -> LeveledHaskType Γ ★) lev l1 l2 q,
    update_ξ ξ lev (app l1 l2) q = update_ξ (update_ξ ξ lev l2) lev l1 q.
    intros.
    induction l1.
      reflexivity.
      simpl.
      destruct a; simpl.
      rewrite IHl1.
      reflexivity.
      Qed.

   Lemma quark {T} (l1:list T) l2 vf :
      (In vf (app l1 l2)) <->
       (In vf l1) \/ (In vf l2).
     induction l1.
     simpl; auto.
     split; intro.
     right; auto.
     inversion H.
     inversion H0.
     auto.
     split.

     destruct IHl1.
     simpl in *.
     intro.
     destruct H1.
     left; left; auto.
     set (H H1) as q.
     destruct q.
     left; right; auto.
     right; auto.
     simpl.

     destruct IHl1.
     simpl in *.
     intro.
     destruct H1.
     destruct H1.
     left; auto.
     right; apply H0; auto.
     right; apply H0; auto.
   Qed.

  Lemma splitter {T} (l1:list T) l2 vf :
      (In vf (app l1 l2) → False)
      -> (In vf l1 → False)  /\ (In vf l2 → False).
    intros.
    split; intros; apply H; rewrite quark.
    auto.
    auto.
    Qed.

  Lemma helper
    : forall T Z {eqdt:EqDecidable T}(tl:Tree ??T)(vf:T) ξ (q:Z),
      (In vf (leaves tl) -> False) ->
      mapOptionTree (fun v' => if eqd_dec vf v' then q else ξ v') tl = 
      mapOptionTree ξ tl.
    intros.
    induction tl;
      try destruct a;
        simpl in *.
    set (eqd_dec vf t) as x in *.
    destruct x.
    subst.
      assert False.
      apply H.
      left; auto.
      inversion H0.
    auto.
    auto.
    apply splitter in H.
    destruct H.
    rewrite (IHtl1 H).
    rewrite (IHtl2 H0).
    reflexivity.
    Qed.
    
  Lemma fresh_lemma' Γ 
    : forall types vars Σ ξ lev, Σ = mapOptionTree ξ vars ->
    FreshM { varstypes : _
      |  mapOptionTree (update_ξ(Γ:=Γ) ξ lev (leaves varstypes)) vars = Σ
      /\ mapOptionTree (update_ξ       ξ lev (leaves varstypes)) (mapOptionTree (@fst _ _) varstypes) = (types @@@ lev)
      /\ distinct (leaves (mapOptionTree (@fst _ _) varstypes)) }.
    induction types.
      intros; destruct a.
        refine (bind vf = fresh (leaves vars) ; return _).
          apply FreshMon.
          destruct vf as [ vf vf_pf ].
          exists [(vf,h)].
          split; auto.
          simpl.
          set (helper VV _ vars vf ξ (h@@lev) vf_pf) as q.
          rewrite q.
          symmetry; auto.
          simpl.
          destruct (eqd_dec vf vf); [ idtac | set (n (refl_equal _)) as n'; inversion n' ]; auto.
          split; auto.
          apply distinct_cons.
          intro.
          inversion H0.
          apply distinct_nil.
        refine (return _).
          exists []; auto.
          split.
          simpl.
          symmetry; auto.
          split.
          simpl.
          reflexivity.
          simpl.
          apply distinct_nil.
        intros vars Σ ξ lev pf; refine (bind x2 = IHtypes2 vars Σ ξ lev pf; _).
          apply FreshMon.
          destruct x2 as [vt2 [pf21 [pf22 pfdist]]].
          refine (bind x1 = IHtypes1 (vars,,(mapOptionTree (@fst _ _) vt2)) (Σ,,(types2@@@lev)) (update_ξ ξ lev
            (leaves vt2)) _ _; return _).
          apply FreshMon.
          simpl.
          rewrite pf21.
          rewrite pf22.
          reflexivity.
          clear IHtypes1 IHtypes2.
          destruct x1 as [vt1 [pf11 pf12]].
          exists (vt1,,vt2); split; auto.

          set (update_branches Γ ξ lev (leaves vt1) (leaves vt2)) as q.
          set (mapOptionTree_extensional _ _ q) as q'.
          rewrite q'.
          clear q' q.
          inversion pf11.
          reflexivity.

          simpl.
          set (update_branches Γ ξ lev (leaves vt1) (leaves vt2)) as q.
          set (mapOptionTree_extensional _ _ q) as q'.
          rewrite q'.
          rewrite q'.
          clear q' q.
          rewrite <- mapOptionTree_compose.
          rewrite <- mapOptionTree_compose.
          rewrite <- mapOptionTree_compose in *.
          split.
          destruct pf12.
          rewrite H.
          inversion pf11.
          rewrite <- mapOptionTree_compose.
          reflexivity.

          admit.
        Defined.

  Lemma fresh_lemma Γ ξ vars Σ Σ' lev
    : Σ = mapOptionTree ξ vars ->
    FreshM { vars' : _
      |  mapOptionTree (update_ξ(Γ:=Γ) ξ lev ((vars',Σ')::nil)) vars = Σ
      /\ mapOptionTree (update_ξ ξ lev ((vars',Σ')::nil)) [vars'] = [Σ' @@ lev] }.
    intros.
    set (fresh_lemma' Γ [Σ'] vars Σ ξ lev H) as q.
    refine (q >>>= fun q' => return _).
    apply FreshMon.
    clear q.
    destruct q' as [varstypes [pf1 [pf2 pfdist]]].
    destruct varstypes; try destruct o; try destruct p; simpl in *.
      destruct (eqd_dec v v); [ idtac | set (n (refl_equal _)) as n'; inversion n' ].    
      inversion pf2; subst.
      exists v.
      destruct (eqd_dec v v); [ idtac | set (n (refl_equal _)) as n'; inversion n' ].
      split; auto.
      inversion pf2.
      inversion pf2.
    Defined.

  Definition urule2expr  : forall Γ Δ h j (r:@URule Γ Δ h j) (ξ:VV -> LeveledHaskType Γ ★),
    ITree _ (ujudg2exprType ξ) h -> ITree _ (ujudg2exprType ξ) j.

      refine (fix urule2expr Γ Δ h j (r:@URule Γ Δ h j) ξ {struct r} : 
        ITree _ (ujudg2exprType ξ) h -> ITree _ (ujudg2exprType ξ) j :=
        match r as R in URule H C return ITree _ (ujudg2exprType ξ) H -> ITree _ (ujudg2exprType ξ) C with
          | RLeft   h c ctx r => let case_RLeft  := tt in (fun e => _) (urule2expr _ _ _ _ r)
          | RRight  h c ctx r => let case_RRight := tt in (fun e => _) (urule2expr _ _ _ _ r)
          | RCanL   t a       => let case_RCanL  := tt in _
          | RCanR   t a       => let case_RCanR  := tt in _
          | RuCanL  t a       => let case_RuCanL := tt in _
          | RuCanR  t a       => let case_RuCanR := tt in _
          | RAssoc  t a b c   => let case_RAssoc := tt in _
          | RCossa  t a b c   => let case_RCossa := tt in _
          | RExch   t a b     => let case_RExch  := tt in _
          | RWeak   t a       => let case_RWeak  := tt in _
          | RCont   t a       => let case_RCont  := tt in _
          end); clear urule2expr; intros.

      destruct case_RCanL.
        apply ILeaf; simpl; intros.
        inversion X.
        simpl in X0.
        apply (X0 ([],,vars)).
        simpl; rewrite <- H; auto.

      destruct case_RCanR.
        apply ILeaf; simpl; intros.
        inversion X.
        simpl in X0.
        apply (X0 (vars,,[])).
        simpl; rewrite <- H; auto.

      destruct case_RuCanL.
        apply ILeaf; simpl; intros.
        destruct vars; try destruct o; inversion H.
        inversion X.
        simpl in X0.
        apply (X0 vars2); auto.

      destruct case_RuCanR.
        apply ILeaf; simpl; intros.
        destruct vars; try destruct o; inversion H.
        inversion X.
        simpl in X0.
        apply (X0 vars1); auto.

      destruct case_RAssoc.
        apply ILeaf; simpl; intros.
        inversion X.
        simpl in X0.
        destruct vars; try destruct o; inversion H.
        destruct vars1; try destruct o; inversion H.
        apply (X0 (vars1_1,,(vars1_2,,vars2))).
        subst; auto.

      destruct case_RCossa.
        apply ILeaf; simpl; intros.
        inversion X.
        simpl in X0.
        destruct vars; try destruct o; inversion H.
        destruct vars2; try destruct o; inversion H.
        apply (X0 ((vars1,,vars2_1),,vars2_2)).
        subst; auto.

      destruct case_RLeft.
        destruct c; [ idtac | apply no_urules_with_multiple_conclusions in r0; inversion r0; exists c1; exists c2; auto ].
        destruct o; [ idtac | apply INone ].
        destruct u; simpl in *.
        apply ILeaf; simpl; intros.
        destruct vars; try destruct o; inversion H.
        set (fun q => ileaf (e ξ q)) as r'.
        simpl in r'.
        apply r' with (vars:=vars2).
        clear r' e.
        clear r0.
        induction h0.
          destruct a.
          destruct u.
          simpl in X.
          apply ileaf in X. 
          apply ILeaf.
          simpl.
          simpl in X.
          intros.
          apply X with (vars:=vars1,,vars).
          simpl.
          rewrite H0.
          rewrite H1.
          reflexivity.
          apply INone.
          apply IBranch.
          apply IHh0_1. inversion X; auto.
          apply IHh0_2. inversion X; auto.
          auto.
        
      destruct case_RRight.
        destruct c; [ idtac | apply no_urules_with_multiple_conclusions in r0; inversion r0; exists c1; exists c2; auto ].
        destruct o; [ idtac | apply INone ].
        destruct u; simpl in *.
        apply ILeaf; simpl; intros.
        destruct vars; try destruct o; inversion H.
        set (fun q => ileaf (e ξ q)) as r'.
        simpl in r'.
        apply r' with (vars:=vars1).
        clear r' e.
        clear r0.
        induction h0.
          destruct a.
          destruct u.
          simpl in X.
          apply ileaf in X. 
          apply ILeaf.
          simpl.
          simpl in X.
          intros.
          apply X with (vars:=vars,,vars2).
          simpl.
          rewrite H0.
          rewrite H2.
          reflexivity.
          apply INone.
          apply IBranch.
          apply IHh0_1. inversion X; auto.
          apply IHh0_2. inversion X; auto.
          auto.

      destruct case_RExch.
        apply ILeaf; simpl; intros.
        inversion X.
        simpl in X0.
        destruct vars; try destruct o; inversion H.
        apply (X0 (vars2,,vars1)).
        inversion H; subst; auto.
        
      destruct case_RWeak.
        apply ILeaf; simpl; intros.
        inversion X.
        simpl in X0.
        apply (X0 []).
        auto.
        
      destruct case_RCont.
        apply ILeaf; simpl; intros.
        inversion X.
        simpl in X0.
        apply (X0 (vars,,vars)).
        simpl.
        rewrite <- H.
        auto.
        Defined.

  Definition bridge Γ Δ (c:Tree ??(UJudg Γ Δ)) ξ :
    ITree Judg judg2exprType (mapOptionTree UJudg2judg c) -> ITree (UJudg Γ Δ) (ujudg2exprType ξ) c.
    intro it.
    induction c.
    destruct a.
      destruct u; simpl in *.
      apply ileaf in it.
      apply ILeaf.
      simpl in *.
      intros; apply it with (vars:=vars); auto.
    apply INone.
    apply IBranch; [ apply IHc1 | apply IHc2 ]; inversion it; auto.
    Defined.

  Definition letrec_helper Γ Δ l (varstypes:Tree ??(VV * HaskType Γ ★)) ξ' :
    ITree (LeveledHaskType Γ ★)
         (fun t : LeveledHaskType Γ ★ => Expr Γ Δ ξ' t)
         (mapOptionTree (ξ' ○ (@fst _ _)) varstypes)
         -> ELetRecBindings Γ Δ ξ' l varstypes.
    intros.
    induction varstypes.
    destruct a; simpl in *.
    destruct p.
    simpl.
    apply ileaf in X. simpl in X.
      apply ELR_leaf.
      rename h into τ.
      destruct (eqd_dec (unlev (ξ' v)) τ).
      rewrite <- e.
      destruct (ξ' v).
      simpl.
      destruct (eqd_dec h0 l).
        rewrite <- e0.
        apply X.
      apply (Prelude_error "level mismatch; should never happen").
      apply (Prelude_error "letrec type mismatch; should never happen").

    apply ELR_nil.
    apply ELR_branch.
      apply IHvarstypes1; inversion X; auto.
      apply IHvarstypes2; inversion X; auto.
    Defined.

  Definition case_helper tc Γ Δ lev tbranches avars ξ (Σ:Tree ??VV) :
    forall pcb : ProofCaseBranch tc Γ Δ lev tbranches avars,
    judg2exprType (pcb_judg pcb) ->
    (pcb_freevars pcb) = mapOptionTree ξ Σ ->
    FreshM
    {scb : StrongCaseBranchWithVVs VV eqdec_vv tc avars &
    Expr (sac_Γ scb Γ) (sac_Δ scb Γ avars (weakCK'' Δ)) 
    (scbwv_ξ scb ξ lev) (weakLT' (tbranches @@  lev))}.

    intros.
    simpl in X.
    destruct pcb.
    simpl in *.
    set (sac_types pcb_scb _ avars) as boundvars.
    refine (fresh_lemma' _ (unleaves (vec2list boundvars)) Σ (mapOptionTree weakLT' pcb_freevars) (weakLT' ○ ξ) (weakL' lev) _
      >>>= fun ξvars => _). apply FreshMon.
    rewrite H.
    rewrite <- mapOptionTree_compose.
    reflexivity.
      destruct ξvars as [ exprvars [pf1 [pf2 pfdistinct]]].
      set (list2vec (leaves (mapOptionTree (@fst _ _) exprvars))) as exprvars'. 

   assert (distinct (vec2list exprvars')) as pfdistinct'.
     unfold exprvars'.
     rewrite vec2list_list2vec.
     apply pfdistinct.

      assert (sac_numExprVars pcb_scb = Datatypes.length (leaves (mapOptionTree (@fst _ _) exprvars))) as H'.
        rewrite <- mapOptionTree_compose in pf2.
        simpl in pf2.
        rewrite mapleaves.
        rewrite <- map_preserves_length.
        rewrite map_preserves_length with (f:=
          (@update_ξ VV eqdec_vv (@sac_Γ tc pcb_scb Γ)
            (@weakLT' Γ (@vec2list (@sac_numExTyVars tc pcb_scb) Kind (@sac_ekinds tc pcb_scb)) ★ ○ ξ)
            (@weakL'  Γ (@vec2list (@sac_numExTyVars tc pcb_scb) Kind (@sac_ekinds tc pcb_scb)) lev)
            (@leaves (VV * HaskType (@sac_Γ tc pcb_scb Γ) ★) exprvars) ○ @fst VV (HaskType (@sac_Γ tc pcb_scb Γ) ★))).
        rewrite <- mapleaves.
        rewrite pf2.       
        rewrite <- mapleaves'.
        rewrite leaves_unleaves.
        rewrite vec2list_map_list2vec.
        rewrite vec2list_len.
        reflexivity.

        clear pfdistinct'.
     rewrite <- H' in exprvars'.
       clear H'.
   assert (distinct (vec2list exprvars')) as pfdistinct'.
     admit.

   set (@Build_StrongCaseBranchWithVVs VV _ tc _ avars pcb_scb exprvars' pfdistinct') as scb.
      set (scbwv_ξ scb ξ lev) as ξ'.
      refine (X ξ' (Σ,,(unleaves (vec2list exprvars'))) _ >>>= fun X' => return _). apply FreshMon.
      simpl.
      unfold ξ'.
      unfold scbwv_ξ.
      simpl.
      admit.

    apply ileaf in X'.
      simpl in X'.
      exists scb.
      unfold weakCK''.
      unfold ξ' in X'.
      apply X'.
    Defined.

  Fixpoint treeM {T}(t:Tree ??(FreshM T)) : FreshM (Tree ??T) :=
    match t with
      | T_Leaf None     => return []
      | T_Leaf (Some x) => bind x' = x ; return [x']
      | T_Branch b1 b2  => bind b1' = treeM b1 ; bind b2' = treeM b2 ; return (b1',,b2')
    end.

  Lemma itree_mapOptionTree : forall T T' F (f:T->T') t,
    ITree _ F (mapOptionTree f t) ->
    ITree _ (F ○ f) t.
    intros.
    induction t; try destruct a; simpl in *.
      apply ILeaf.
      inversion X; auto.
      apply INone.
      apply IBranch.
        apply IHt1; inversion X; auto.
        apply IHt2; inversion X; auto.
        Defined.

  Definition rule2expr : forall h j (r:Rule h j), ITree _ judg2exprType h -> ITree _ judg2exprType j.

    intros h j r.

      refine (match r as R in Rule H C return ITree _ judg2exprType H -> ITree _ judg2exprType C with
      | RURule a b c d e              => let case_RURule := tt        in _
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
      end); intro X_; try apply ileaf in X_; simpl in X_.

  destruct case_RURule.
    destruct d; try destruct o.
      apply ILeaf; destruct u; simpl; intros.
      set (@urule2expr a b _ _ e ξ) as q.
      set (fun z => ileaf (q z)) as q'.
      simpl in q'.
      apply q' with (vars:=vars).
      clear q' q.
      apply bridge.
      apply X_.
      auto.
      apply no_urules_with_empty_conclusion in e; inversion e; auto.
      apply no_urules_with_multiple_conclusions in e; inversion e; auto; exists d1; exists d2; auto.

  destruct case_RBrak.
    apply ILeaf; simpl; intros; refine (X_ ξ vars H >>>= fun X => return ILeaf _ _). apply FreshMon.
    apply EBrak.
    apply (ileaf X).

  destruct case_REsc.
    apply ILeaf; simpl; intros; refine (X_ ξ vars H >>>= fun X => return ILeaf _ _). apply FreshMon.
    apply EEsc.
    apply (ileaf X).

  destruct case_RNote.
    apply ILeaf; simpl; intros; refine (X_ ξ vars H >>>= fun X => return ILeaf _ _). apply FreshMon.
    apply ENote; auto.
    apply (ileaf X).

  destruct case_RLit.
    apply ILeaf; simpl; intros; refine (return ILeaf _ _).
    apply ELit.

  destruct case_RVar.
    apply ILeaf; simpl; intros; refine (return ILeaf _ _).
    destruct vars; simpl in H; inversion H; destruct o. inversion H1. rewrite H2.
    apply EVar.
    inversion H.

  destruct case_RGlobal.
    apply ILeaf; simpl; intros; refine (return ILeaf _ _).
    apply EGlobal.
    apply wev.

  destruct case_RLam.
    apply ILeaf.
    simpl in *; intros.
    refine (fresh_lemma _ ξ vars _ tx x H >>>= (fun pf => _)).
    apply FreshMon.
    destruct pf as [ vnew [ pf1 pf2 ]].
    set (update_ξ ξ x ((⟨vnew, tx  ⟩) :: nil)) as ξ' in *.
    refine (X_ ξ' (vars,,[vnew]) _ >>>= _).
    apply FreshMon.
    simpl.
    rewrite pf1.
    rewrite <- pf2.
    simpl.
    reflexivity.
    intro hyp.
    refine (return _).
    apply ILeaf.
    apply ELam with (ev:=vnew).
    apply ileaf in hyp.
    simpl in hyp.
    unfold ξ' in hyp.
    apply hyp.

  destruct case_RCast.
    apply ILeaf; simpl; intros; refine (X_ ξ vars H >>>= fun X => return ILeaf _ _). apply FreshMon.
    eapply ECast.
    apply x.
    apply ileaf in X. simpl in X.
    apply X.

  destruct case_RBindingGroup.
    apply ILeaf; simpl; intros.
    inversion X_.
    apply ileaf in X.
    apply ileaf in X0.
    simpl in *.
    destruct vars; inversion H.
    destruct o; inversion H3.
    refine (X ξ vars1 H3 >>>= fun X' => X0 ξ vars2 H4 >>>= fun X0' => return _).
    apply FreshMon.
    apply FreshMon.
    apply IBranch; auto.

  destruct case_RApp.    
    apply ILeaf.
    inversion X_.
    inversion X.
    inversion X0.
    simpl in *.
    intros.
    destruct vars. try destruct o; inversion H.
    simpl in H.
    inversion H.
    set (X1 ξ vars1 H5) as q1.
    set (X2 ξ vars2 H6) as q2.
    refine (q1 >>>= fun q1' => q2 >>>= fun q2' => return _).
    apply FreshMon.
    apply FreshMon.
    apply ILeaf.
    apply ileaf in q1'.
    apply ileaf in q2'.
    simpl in *.
    apply (EApp _ _ _ _ _ _ q1' q2').

  destruct case_RLet.
    apply ILeaf.
    simpl in *; intros.
    destruct vars; try destruct o; inversion H.
    refine (fresh_lemma _ ξ vars1 _ σ₂ p H1 >>>= (fun pf => _)).
    apply FreshMon.
    destruct pf as [ vnew [ pf1 pf2 ]].
    set (update_ξ ξ p ((⟨vnew, σ₂  ⟩) :: nil)) as ξ' in *.
    inversion X_.
    apply ileaf in X.
    apply ileaf in X0.
    simpl in *.
    refine (X0 ξ  vars2 _ >>>= fun X0' => _).
    apply FreshMon.
    auto.
    refine (X  ξ' (vars1,,[vnew]) _ >>>= fun X1' => _).
    apply FreshMon.
    rewrite H1.
    simpl.
    rewrite pf2.
    rewrite pf1.
    rewrite H1.
    reflexivity.
    refine (return _).
    apply ILeaf.
    apply ileaf in X0'.
    apply ileaf in X1'.
    simpl in *.
    apply ELet with (ev:=vnew)(tv:=σ₂).
    apply X0'.
    apply X1'.

  destruct case_REmptyGroup.
    apply ILeaf; simpl; intros.
    refine (return _).
    apply INone.

  destruct case_RAppT.
    apply ILeaf; simpl; intros; refine (X_ ξ vars H >>>= fun X => return ILeaf _ _). apply FreshMon.
    apply ETyApp.
    apply (ileaf X).

  destruct case_RAbsT.
    apply ILeaf; simpl; intros; refine (X_ (weakLT ○ ξ) vars _ >>>= fun X => return ILeaf _ _). apply FreshMon.
    rewrite mapOptionTree_compose.
    rewrite <- H.
    reflexivity.
    apply ileaf in X. simpl in *.
    apply ETyLam.
    apply X.

  destruct case_RAppCo.
    apply ILeaf; simpl; intros; refine (X_ ξ vars _ >>>= fun X => return ILeaf _ _). apply FreshMon.
    auto.
    eapply ECoApp.
    apply γ.
    apply (ileaf X).

  destruct case_RAbsCo.
    apply ILeaf; simpl; intros; refine (X_ ξ vars _ >>>= fun X => return ILeaf _ _). apply FreshMon.
    auto.
    eapply ECoLam.
    apply (ileaf X).

  destruct case_RLetRec.
    apply ILeaf; simpl; intros.
    refine (bind ξvars = fresh_lemma' _ y _ _ _ t H; _). apply FreshMon.
    destruct ξvars as [ varstypes [ pf1[ pf2 pfdist]]].
    refine (X_ ((update_ξ ξ t (leaves varstypes)))
      (vars,,(mapOptionTree (@fst _ _) varstypes)) _ >>>= fun X => return _); clear X_.  apply FreshMon.
    simpl.
    rewrite pf2.
    rewrite pf1.
    auto.
    apply ILeaf.
    inversion X; subst; clear X.

    apply (@ELetRec _ _ _ _ _ _ _ varstypes).
    apply (@letrec_helper Γ Δ t varstypes).
    rewrite <- pf2 in X1.
    rewrite mapOptionTree_compose.
    apply X1.
    apply ileaf in X0.
    apply X0.

  destruct case_RCase.
    apply ILeaf; simpl; intros.
    inversion X_.
    clear X_.
    subst.
    apply ileaf in X0.
    simpl in X0.
    set (mapOptionTreeAndFlatten pcb_freevars alts) as Σalts in *.
    refine (bind ξvars = fresh_lemma' _ (mapOptionTree unlev (Σalts,,Σ)) _ _ _ lev H ; _).
      apply FreshMon.
      destruct vars; try destruct o; inversion H; clear H.
      rename vars1 into varsalts.
      rename vars2 into varsΣ.

    refine ( _ >>>= fun Y => X0 ξ varsΣ _ >>>= fun X => return ILeaf _ (@ECase _ _ _ _ _ _ _ _ _ (ileaf X) Y)); auto.
      apply FreshMon.
      destruct ξvars as [varstypes [pf1 pf2]].

      apply treeM.
      apply itree_mapOptionTree in X.
      refine (itree_to_tree (itmap _ X)).
      intros.
      eapply case_helper.
      apply X1.
      instantiate (1:=varsΣ).
      rewrite <- H2.
      admit.
      apply FreshMon.
    Defined.

  Definition closed2expr : forall c (pn:@ClosedND _ Rule c), ITree _ judg2exprType c.
    refine ((
      fix closed2expr' j (pn:@ClosedND _ Rule j) {struct pn} : ITree _ judg2exprType j :=
      match pn in @ClosedND _ _ J return ITree _ judg2exprType J with
      | cnd_weak             => let case_nil    := tt in INone _ _
      | cnd_rule h c cnd' r  => let case_rule   := tt in rule2expr _ _ r (closed2expr' _ cnd')
      | cnd_branch _ _ c1 c2 => let case_branch := tt in IBranch _ _ (closed2expr' _ c1) (closed2expr' _ c2)
      end)); clear closed2expr'; intros; subst.
        Defined.

  Lemma manyFresh : forall Γ Σ (ξ0:VV -> LeveledHaskType Γ ★),
    FreshM { vars : _ & { ξ : VV -> LeveledHaskType Γ ★ & Σ = mapOptionTree ξ vars } }.
    intros Γ Σ.
    induction Σ; intro ξ.
    destruct a.
    destruct l as [τ l].
    set (fresh_lemma' Γ [τ] [] [] ξ l (refl_equal _)) as q.
    refine (q >>>= fun q' => return _).
    apply FreshMon.
    clear q.
    destruct q' as [varstypes [pf1 [pf2 distpf]]].
    exists (mapOptionTree (@fst _ _) varstypes).
    exists (update_ξ ξ l (leaves varstypes)).
    symmetry; auto.
    refine (return _).
    exists [].
    exists ξ; auto.
    refine (bind f1 = IHΣ1 ξ ; _).
    apply FreshMon.
    destruct f1 as [vars1 [ξ1 pf1]].
    refine (bind f2 = IHΣ2 ξ1 ; _).
    apply FreshMon.
    destruct f2 as [vars2 [ξ2 pf22]].
    refine (return _).
    exists (vars1,,vars2).
    exists ξ2.
    simpl.
    rewrite pf22.
    rewrite pf1.
    admit.
    Defined.

  Definition proof2expr Γ Δ τ Σ (ξ0: VV -> LeveledHaskType Γ ★)
    {zz:ToString VV} : ND Rule [] [Γ > Δ > Σ |- [τ]] ->
    FreshM (???{ ξ : _ & Expr Γ Δ ξ τ}).
    intro pf.
    set (closedFromSCND _ _ (mkSCND systemfc_all_rules_one_conclusion _ _ _ pf (scnd_weak [])) cnd_weak) as cnd.
    apply closed2expr in cnd.
    apply ileaf in cnd.
    simpl in *.
    clear pf.
    refine (bind ξvars = manyFresh _ Σ ξ0; _).
    apply FreshMon.
    destruct ξvars as [vars ξpf].
    destruct ξpf as [ξ pf].
    refine (cnd ξ vars _ >>>= fun it => _).
    apply FreshMon.
    auto.
    refine (return OK _).
    exists ξ.
    apply (ileaf it).
    Defined.

End HaskProofToStrong.
