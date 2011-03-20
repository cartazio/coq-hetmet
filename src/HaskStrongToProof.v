(*********************************************************************************************************************************)
(* HaskStrongToProof: convert HaskStrong to HaskProof                                                                            *)
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

Section HaskStrongToProof.

(* Whereas RLeft/RRight perform left and right context expansion on a single uniform rule, these functions perform
 * expansion on an entire uniform proof *)
Definition ext_left  {Γ}{Δ}(ctx:Tree ??(LeveledHaskType Γ ★))
  := @nd_map' _ _ _ _ (ext_tree_left ctx)  (fun h c r => nd_rule (@RLeft Γ Δ h c ctx r)).
Definition ext_right {Γ}{Δ}(ctx:Tree ??(LeveledHaskType Γ ★))
  := @nd_map' _ _ _ _ (ext_tree_right ctx) (fun h c r => nd_rule (@RRight Γ Δ h c ctx r)).

Definition pivotContext {Γ}{Δ} a b c τ :
  @ND _ (@URule Γ Δ)
    [ Γ >> Δ > (a,,b),,c |- τ]
    [ Γ >> Δ > (a,,c),,b |- τ].
  set (ext_left a _ _ (nd_rule (@RExch Γ Δ τ c b))) as q.
  simpl in *.
  eapply nd_comp ; [ eapply nd_rule; apply RCossa | idtac ]. 
  eapply nd_comp ; [ idtac | eapply nd_rule; apply RAssoc ].
  apply q.
  Defined.

Definition copyAndPivotContext {Γ}{Δ} a b c τ :
  @ND _ (@URule Γ Δ)
    [ Γ >> Δ > (a,,b),,(c,,b) |- τ]
    [ Γ >> Δ > (a,,c),,b |- τ].
    set (ext_left (a,,c) _ _ (nd_rule (@RCont Γ Δ τ b))) as q.
    simpl in *.
    eapply nd_comp; [ idtac | apply q ].
    clear q.
    eapply nd_comp ; [ idtac | eapply nd_rule; apply RCossa ].
    set (ext_right b _ _ (@pivotContext _ Δ a b c τ)) as q.
    simpl in *.
    eapply nd_comp ; [ idtac | apply q ]. 
    clear q.
    apply nd_rule.
    apply RAssoc.
    Defined.


  
Context {VV:Type}{eqd_vv:EqDecidable VV}.

  (* maintenance of Xi *)
  Fixpoint dropVar (lv:list VV)(v:VV) : ??VV :=
    match lv with
      | nil     => Some v
      | v'::lv' => if eqd_dec v v' then None else dropVar lv' v
    end.
  (* later: use mapOptionTreeAndFlatten *)
  Definition stripOutVars (lv:list VV) : Tree ??VV -> Tree ??VV :=
    mapTree (fun x => match x with None => None | Some vt => dropVar lv vt end).

Fixpoint expr2antecedent {Γ'}{Δ'}{ξ'}{τ'}(exp:Expr Γ' Δ' ξ' τ') : Tree ??VV :=
  match exp as E in Expr Γ Δ ξ τ with
  | EGlobal  Γ Δ ξ _ _                            => []
  | EVar     Γ Δ ξ ev                             => [ev]
  | ELit     Γ Δ ξ lit lev                        => []
  | EApp     Γ Δ ξ t1 t2 lev e1 e2                => (expr2antecedent e1),,(expr2antecedent e2)
  | ELam     Γ Δ ξ t1 t2 lev v    e               => stripOutVars (v::nil) (expr2antecedent e)
  | ELet     Γ Δ ξ tv t  lev v ev ebody           => ((stripOutVars (v::nil) (expr2antecedent ebody)),,(expr2antecedent ev))
  | EEsc     Γ Δ ξ ec t lev e                     => expr2antecedent e
  | EBrak    Γ Δ ξ ec t lev e                     => expr2antecedent e
  | ECast    Γ Δ ξ γ t1 t2 lev      e             => expr2antecedent e
  | ENote    Γ Δ ξ t n e                          => expr2antecedent e
  | ETyLam   Γ Δ ξ κ σ l e                        => expr2antecedent e
  | ECoLam   Γ Δ κ σ σ₁ σ₂ ξ l             e      => expr2antecedent e
  | ECoApp   Γ Δ κ γ σ₁ σ₂ σ ξ l      e           => expr2antecedent e
  | ETyApp   Γ Δ κ σ τ ξ  l    e                  => expr2antecedent e
  | ELetRec  Γ Δ ξ l τ vars branches body         =>
      let branch_context := eLetRecContext branches
   in let all_contexts := (expr2antecedent body),,branch_context
   in     stripOutVars (leaves (mapOptionTree (@fst _ _ ) vars)) all_contexts
  | ECase    Γ Δ ξ l tc tbranches atypes e' alts =>
    ((fix varsfromalts (alts:
               Tree ??{ scb : StrongCaseBranchWithVVs _ _ tc atypes
                            & Expr (sac_Γ scb Γ)
                                   (sac_Δ scb Γ atypes (weakCK'' Δ))
                                   (scbwv_ξ scb ξ l)
                                   (weakLT' (tbranches@@l)) }
      ): Tree ??VV :=
      match alts with
        | T_Leaf None     => []
        | T_Leaf (Some h) => stripOutVars (vec2list (scbwv_exprvars (projT1 h))) (expr2antecedent (projT2 h))
        | T_Branch b1 b2  => (varsfromalts b1),,(varsfromalts b2)
      end) alts),,(expr2antecedent e')
end
with eLetRecContext {Γ}{Δ}{ξ}{lev}{tree}(elrb:ELetRecBindings Γ Δ ξ lev tree) : Tree ??VV :=
match elrb with
  | ELR_nil    Γ Δ ξ lev  => []
  | ELR_leaf   Γ Δ ξ lev v t e => expr2antecedent e
  | ELR_branch Γ Δ ξ lev t1 t2 b1 b2 => (eLetRecContext b1),,(eLetRecContext b2)
end.

Definition mkProofCaseBranch {Γ}{Δ}{ξ}{l}{tc}{tbranches}{atypes}
  (alt: { scb : StrongCaseBranchWithVVs _ _ tc atypes
                            & Expr (sac_Γ scb Γ)
                                   (sac_Δ scb Γ atypes (weakCK'' Δ))
                                   (scbwv_ξ scb ξ l)
                                   (weakLT' (tbranches@@l)) })
  : ProofCaseBranch tc Γ Δ l tbranches atypes.
  exact
    {| pcb_scb := projT1 alt
     ; pcb_freevars := mapOptionTree ξ (stripOutVars (vec2list (scbwv_exprvars (projT1 alt))) (expr2antecedent (projT2 alt)))
     |}.
     Defined.


Fixpoint eLetRecTypes {Γ}{Δ}{ξ}{lev}{τ}(elrb:ELetRecBindings Γ Δ ξ lev τ) : Tree ??(HaskType Γ ★) :=
  match elrb with
  | ELR_nil    Γ Δ ξ lev  => []
  | ELR_leaf   Γ Δ ξ  lev  v t e => [t]
  | ELR_branch Γ Δ ξ lev t1 t2 b1 b2 => (eLetRecTypes b1),,(eLetRecTypes b2)
  end.
(*
Fixpoint eLetRecVars {Γ}{Δ}{ξ}{lev}{τ}(elrb:ELetRecBindings Γ Δ ξ lev τ) : Tree ??VV :=
  match elrb with
  | ELR_nil    Γ Δ ξ lev  => []
  | ELR_leaf   Γ Δ ξ  lev  v _ _ e => [v]
  | ELR_branch Γ Δ ξ lev t1 t2 b1 b2 => (eLetRecVars b1),,(eLetRecVars b2)
  end.

Fixpoint eLetRecTypesVars {Γ}{Δ}{ξ}{lev}{τ}(elrb:ELetRecBindings Γ Δ ξ lev τ) : Tree ??(VV * HaskType Γ ★):=
  match elrb with
  | ELR_nil    Γ Δ ξ lev  => []
  | ELR_leaf   Γ Δ ξ  lev  v t _ e => [(v, t)]
  | ELR_branch Γ Δ ξ lev t1 t2 b1 b2 => (eLetRecTypesVars b1),,(eLetRecTypesVars b2)
  end.
*)

Lemma stripping_nothing_is_inert
  {Γ:TypeEnv}
  (ξ:VV -> LeveledHaskType Γ ★)
  tree :
  stripOutVars nil tree = tree.
  induction tree.
    simpl; destruct a; reflexivity.
    unfold stripOutVars.
    fold stripOutVars.
    simpl.
    fold (stripOutVars nil).
    rewrite <- IHtree1 at 2.
    rewrite <- IHtree2 at 2.
    reflexivity.
    Qed.

Ltac eqd_dec_refl X :=
  destruct (eqd_dec X X) as [eqd_dec1 | eqd_dec2];
    [ clear eqd_dec1 | set (eqd_dec2 (refl_equal _)) as eqd_dec2'; inversion eqd_dec2' ].

Definition arrangeContext 
     (Γ:TypeEnv)(Δ:CoercionEnv Γ)
     v      (* variable to be pivoted, if found *)
     ctx    (* initial context *)
     τ      (* type of succedent *)
     (ξ:VV -> LeveledHaskType Γ ★)
     :
 
    (* a proof concluding in a context where that variable does not appear *)
    sum (ND (@URule Γ Δ)
          [Γ >> Δ > mapOptionTree ξ                        ctx                        |- τ]
          [Γ >> Δ > mapOptionTree ξ (stripOutVars (v::nil) ctx),,[]                   |- τ])
   
    (* or a proof concluding in a context where that variable appears exactly once in the left branch *)
        (ND (@URule Γ Δ)
          [Γ >> Δ > mapOptionTree ξ                         ctx                       |- τ]
          [Γ >> Δ > mapOptionTree ξ ((stripOutVars (v::nil) ctx),,[v])                |- τ]).

  induction ctx.
  
    refine (match a with None => let case_None := tt in _ | Some v' => let case_Some := tt in _ end).
  
        (* nonempty leaf *)
        destruct case_Some.
          unfold stripOutVars in *; simpl.
          unfold dropVar.
          unfold mapOptionTree in *; simpl; fold (mapOptionTree ξ) in *.

          destruct (eqd_dec v' v); subst.
          
            (* where the leaf is v *)
            apply inr.
              subst.
              apply nd_rule.
              apply RuCanL.

            (* where the leaf is NOT v *)
            apply inl.
              apply nd_rule.
              apply RuCanR.
  
        (* empty leaf *)
        destruct case_None.
          apply inl; simpl in *.
          apply nd_rule.
          apply RuCanR.
  
      (* branch *)
      refine (
        match IHctx1 with
          | inr lpf =>
            match IHctx2 with
              | inr rpf => let case_Both := tt in _
              | inl rpf => let case_Left := tt in _
            end
          | inl lpf =>
            match IHctx2 with
              | inr rpf => let case_Right   := tt in _
              | inl rpf => let case_Neither := tt in _
            end
        end); clear IHctx1; clear IHctx2.

    destruct case_Neither.
      apply inl.
      eapply nd_comp; [idtac | eapply nd_rule; apply RuCanR ].
        exact (nd_comp
          (* order will not matter because these are central as morphisms *)
          (ext_right _ _ _ (nd_comp lpf (nd_rule (@RCanR _ _ _ _))))
          (ext_left  _ _ _ (nd_comp rpf (nd_rule (@RCanR _ _ _ _))))).


    destruct case_Right.
      apply inr.
      fold (stripOutVars (v::nil)).
      set (ext_right (mapOptionTree ξ ctx2) _ _ (nd_comp lpf (nd_rule (@RCanR _ _ _ _)))) as q.
      simpl in *.
      eapply nd_comp.
      apply q.
      clear q.
      clear lpf.
      unfold mapOptionTree in *; simpl; fold (mapOptionTree ξ) in *.
      eapply nd_comp; [ idtac | eapply nd_rule; apply RAssoc ].
      set (ext_left (mapOptionTree ξ (stripOutVars (v :: nil) ctx1)) [Γ >> Δ>mapOptionTree ξ ctx2 |- τ]
                                                            [Γ >> Δ> (mapOptionTree ξ (stripOutVars (v :: nil) ctx2),,[ξ v])  |- τ]) as qq.
      apply qq.
      clear qq.
      apply rpf.

    destruct case_Left.
      apply inr.
      unfold mapOptionTree in *; simpl; fold (mapOptionTree ξ) in *.
      fold (stripOutVars (v::nil)).
      eapply nd_comp; [ idtac | eapply pivotContext ].
      set (nd_comp rpf (nd_rule (@RCanR _ _ _ _ ) ) ) as rpf'.
      set (ext_left ((mapOptionTree ξ (stripOutVars (v :: nil) ctx1),, [ξ v])) _ _ rpf') as qq.
      simpl in *.
      eapply nd_comp; [ idtac | apply qq ].
      clear qq rpf' rpf.
      set (ext_right (mapOptionTree ξ ctx2) [Γ >>Δ> mapOptionTree ξ ctx1 |- τ] [Γ >>Δ> (mapOptionTree ξ (stripOutVars (v :: nil) ctx1),, [ξ v]) |- τ]) as q.
      apply q.
      clear q.
      apply lpf.

    destruct case_Both.
      apply inr.
      unfold mapOptionTree in *; simpl; fold (mapOptionTree ξ) in *.
      fold (stripOutVars (v::nil)).
      eapply nd_comp; [ idtac | eapply copyAndPivotContext ].
        exact (nd_comp
          (* order will not matter because these are central as morphisms *)
          (ext_right _ _ _ lpf)
          (ext_left  _ _ _ rpf)).

    Defined.

(* same as before, but use RWeak if necessary *)
Definition arrangeContextAndWeaken v ctx Γ Δ τ ξ : 
       ND (@URule Γ Δ)
          [Γ >> Δ>mapOptionTree ξ                        ctx                |- τ]
          [Γ >> Δ>mapOptionTree ξ ((stripOutVars (v::nil) ctx),,[v])        |- τ].
  set (arrangeContext Γ Δ v ctx τ ξ) as q.
  destruct q; auto.
  eapply nd_comp; [ apply n | idtac ].
  clear n.
  refine (ext_left _ _ _ (nd_rule (RWeak _ _))).
  Defined.

Lemma strip_lemma a x t : stripOutVars (a::x) t = stripOutVars (a::nil) (stripOutVars x t).
  unfold stripOutVars.
  rewrite <- mapTree_compose.
  induction t; try destruct a0.
  simpl.
  induction x.
    reflexivity.
    admit.
  subst.
  reflexivity.
  simpl in *.
  rewrite <- IHt1.
  rewrite <- IHt2.
  reflexivity.
  Qed.

Lemma strip_twice_lemma x y t : stripOutVars x (stripOutVars y t) = stripOutVars (app y x) t.
  induction x.
  simpl.
  admit.
  rewrite strip_lemma.
  rewrite IHx.
  rewrite <- strip_lemma.
  admit.
  Qed.

Lemma distinct_app1 : forall T (l1 l2:list T), distinct (app l1 l2) -> distinct l1.
  admit.
  Qed.

Lemma distinct_app2 : forall T (l1 l2:list T), distinct (app l1 l2) -> distinct l2.
  admit.
  Qed.

Lemma strip_distinct x y : distinct (app (leaves y) x) -> stripOutVars x y = y.
  admit.
  Qed.

Definition arrangeContextAndWeaken'' Γ Δ ξ v : forall ctx z, 
  distinct (leaves v) ->
  ND (@URule Γ Δ)
    [Γ >> Δ>(mapOptionTree ξ ctx)                                       |-  z]
    [Γ >> Δ>(mapOptionTree ξ (stripOutVars (leaves v) ctx)),,(mapOptionTree ξ v) |-  z].

  induction v; intros.
    destruct a.
    unfold mapOptionTree in *.
    simpl in *.
    fold (mapOptionTree ξ) in *.
    intros.
    apply arrangeContextAndWeaken.

  unfold mapOptionTree; simpl in *.
    intros.
    rewrite (@stripping_nothing_is_inert Γ); auto.
    apply nd_rule.
    apply RuCanR.
    intros.
    unfold mapOptionTree in *.
    simpl in *.
    fold (mapOptionTree ξ) in *.
    set (mapOptionTree ξ) as X in *.

    set (IHv2 ((stripOutVars (leaves v1) ctx),, v1) z) as IHv2'.
    unfold stripOutVars in IHv2'.
    simpl in IHv2'.
    fold (stripOutVars (leaves v2)) in IHv2'.
    fold (stripOutVars (leaves v1)) in IHv2'.
    unfold X in IHv2'.
    unfold mapOptionTree in IHv2'.
    simpl in IHv2'.
    fold (mapOptionTree ξ) in IHv2'.
    fold X in IHv2'.
    set (nd_comp (IHv1 _ _ (distinct_app1 _ _ _ H)) (IHv2' (distinct_app2 _ _ _ H))) as qq.
    eapply nd_comp.
      apply qq.
      clear qq IHv2' IHv2 IHv1.
      rewrite strip_twice_lemma.

      rewrite (strip_distinct (leaves v2) v1).
        apply nd_rule.
        apply RCossa.
        auto.
    Defined.

Lemma updating_stripped_tree_is_inert {Γ} (ξ:VV -> LeveledHaskType Γ ★) v tree t lev :
      mapOptionTree (update_ξ ξ lev ((v,t)::nil)) (stripOutVars (v :: nil) tree)
    = mapOptionTree ξ (stripOutVars (v :: nil) tree).
  induction tree; simpl in *; try reflexivity; auto.

  unfold mapOptionTree in *; simpl; fold (mapOptionTree ξ) in *; fold (mapOptionTree (update_ξ ξ lev ((v,t)::nil))) in *.
  destruct a; simpl; try reflexivity.
  unfold update_ξ.
  simpl.
  unfold mapOptionTree in *; simpl; fold (mapOptionTree ξ) in *.
  unfold update_ξ.
  unfold dropVar.
  simpl.
  set (eqd_dec v v0) as q.
  assert (q=eqd_dec v v0).
    reflexivity.
  destruct q.
(*
  reflexivity.
  rewrite <- H.
  reflexivity.
  auto.
  unfold mapOptionTree.
  unfold mapOptionTree in IHtree1.
  unfold mapOptionTree in IHtree2.
  simpl in *.
  simpl in IHtree1.
  fold (stripOutVars (v::nil)).
  rewrite <- IHtree1.
  rewrite <- IHtree2.
  reflexivity.
*)
admit.
admit.
admit.
  Qed.


Lemma updating_stripped_tree_is_inert'
  {Γ} lev
  (ξ:VV -> LeveledHaskType Γ ★)
  tree tree2 :
    mapOptionTree (update_ξ ξ lev (leaves tree)) (stripOutVars (leaves (mapOptionTree (@fst _ _) tree)) tree2)
  = mapOptionTree ξ (stripOutVars (leaves (mapOptionTree (@fst _ _) tree)) tree2).
  admit.
  Qed.

Lemma updating_stripped_tree_is_inert''' : forall Γ tc ξ l t atypes x,
         mapOptionTree (scbwv_ξ(Γ:=Γ)(tc:=tc)(atypes:=atypes) x ξ l)
           (stripOutVars (vec2list (scbwv_exprvars x)) t)
             =
         mapOptionTree (weakLT' ○ ξ)
           (stripOutVars (vec2list (scbwv_exprvars x)) t).
  intros.
  unfold scbwv_ξ.
  unfold scbwv_varstypes.
  admit.
  Qed.

(* IDEA: use multi-conclusion proofs instead *)
Inductive LetRecSubproofs Γ Δ ξ lev : forall tree, ELetRecBindings Γ Δ ξ lev tree -> Type := 
  | lrsp_nil  : LetRecSubproofs Γ Δ ξ lev [] (ELR_nil _ _ _ _)
  | lrsp_leaf : forall v t e ,
    (ND Rule [] [Γ > Δ > mapOptionTree ξ (expr2antecedent e) |- [t@@lev]]) ->
    LetRecSubproofs Γ Δ ξ lev [(v, t)] (ELR_leaf _ _ _ _ _ t e)
  | lrsp_cons : forall t1 t2 b1 b2,
    LetRecSubproofs Γ Δ ξ lev t1 b1 ->
    LetRecSubproofs Γ Δ ξ lev t2 b2 ->
    LetRecSubproofs Γ Δ ξ lev (t1,,t2) (ELR_branch _ _ _ _ _ _ b1 b2).

Lemma letRecSubproofsToND Γ Δ ξ lev tree branches :
  LetRecSubproofs Γ Δ ξ lev tree branches ->
    ND Rule [] [ Γ > Δ > mapOptionTree ξ (eLetRecContext branches)
      |- eLetRecTypes branches @@@ lev ].
  intro X; induction X; intros; simpl in *.
    apply nd_rule.
      apply REmptyGroup.
    set (ξ v) as q in *.
      destruct q.
      simpl in *.
      apply n.
    eapply nd_comp; [ idtac | eapply nd_rule; apply RBindingGroup ].
    eapply nd_comp; [ apply nd_llecnac | idtac ].
    apply nd_prod; auto.
  Defined.

Lemma letRecSubproofsToND' Γ Δ ξ lev τ tree  :
    forall branches body,
    ND Rule [] [Γ > Δ > mapOptionTree (update_ξ ξ lev (leaves tree)) (expr2antecedent body) |- [τ @@ lev]] -> 
    LetRecSubproofs Γ Δ (update_ξ ξ lev (leaves tree)) lev tree branches ->
    ND Rule [] [Γ > Δ > mapOptionTree ξ (expr2antecedent (@ELetRec VV _ Γ Δ ξ lev τ tree branches body)) |- [τ @@ lev]].

  (* NOTE: how we interpret stuff here affects the order-of-side-effects *)
  intro branches.
  intro body.
  intro pf.
  intro lrsp.
  set ((update_ξ ξ lev (leaves tree))) as ξ' in *.
  set ((stripOutVars (leaves (mapOptionTree (@fst _ _) tree)) (eLetRecContext branches))) as ctx.
  set (mapOptionTree (@fst _ _) tree) as pctx.
  set (mapOptionTree ξ' pctx) as passback.
  set (fun a b => @RLetRec Γ Δ a b (mapOptionTree (@snd _ _) tree)) as z.
  eapply nd_comp; [ idtac | eapply nd_rule; apply z ].
  clear z.

  set (@arrangeContextAndWeaken''  Γ Δ ξ' pctx (expr2antecedent body,,eLetRecContext branches)) as q'.
  unfold passback in *; clear passback.
  unfold pctx in *; clear pctx.
  eapply UND_to_ND in q'.

  unfold ξ' in *.
  set (@updating_stripped_tree_is_inert') as zz.
  rewrite zz in q'.
  clear zz.
  clear ξ'.
  Opaque stripOutVars.
  simpl.
  rewrite <- mapOptionTree_compose in q'.
  cut ((mapOptionTree (update_ξ ξ lev (leaves tree) ○ (@fst _ _)) tree) = (mapOptionTree (@snd _ _) tree @@@ lev)).
  intro H'.
  rewrite <- H'.
  eapply nd_comp; [ idtac | apply q' ].
  clear H'.
  clear q'.
  simpl.

  set (letRecSubproofsToND _ _ _ _ _ branches lrsp) as q.
    eapply nd_comp; [ idtac | eapply nd_rule; apply RBindingGroup ].
    eapply nd_comp; [ apply nd_llecnac | idtac ].
    apply nd_prod; auto.
    cut ((eLetRecTypes branches @@@ lev) = mapOptionTree (update_ξ ξ lev (leaves tree) ○ (@fst _ _)) tree).
      intro H''.
      rewrite <- H''.
    apply q.
  admit.
  admit.
  admit.
  Defined.

Lemma update_ξ_lemma `{EQD_VV:EqDecidable VV} : forall Γ ξ (lev:HaskLevel Γ)(varstypes:list (VV*_)),
  distinct (map (@fst _ _) varstypes) ->
  map (update_ξ ξ lev varstypes) (map (@fst _ _) varstypes) =
  map (fun t => t@@ lev) (map (@snd _ _) varstypes).
  intros.
  induction varstypes.
  reflexivity.
  destruct a.
  inversion H.
  subst.
  admit.
  Qed.

Lemma fst_zip : forall T Q n (v1:vec T n)(v2:vec Q n), vec_map (@fst _ _) (vec_zip v1 v2) = v1.
  admit.
  Qed.

Lemma snd_zip : forall T Q n (v1:vec T n)(v2:vec Q n), vec_map (@snd _ _) (vec_zip v1 v2) = v2.
  admit.
  Defined.

Lemma vec2list_injective : forall T n (v1 v2:vec T n), vec2list v1 = vec2list v2 -> v1 = v2.
  admit.
  Defined.

Lemma scbwv_coherent {tc}{Γ}{atypes:IList _ (HaskType Γ) _} :
  forall scb:StrongCaseBranchWithVVs _ _ tc atypes,
    forall l ξ, vec_map (scbwv_ξ scb ξ l) (scbwv_exprvars scb) =
                                 vec_map (fun t => t @@ weakL' l) (sac_types (scbwv_sac scb) _ atypes).
  intros.
  unfold scbwv_ξ.
  unfold scbwv_varstypes.
  set (@update_ξ_lemma _ _ (weakLT' ○ ξ) (weakL' l)
    (vec2list (vec_zip (scbwv_exprvars scb) (sac_types (scbwv_sac scb) Γ atypes)))) as q.
  rewrite vec2list_map_list2vec in q.
  rewrite fst_zip in q.
  rewrite vec2list_map_list2vec in q.
  rewrite vec2list_map_list2vec in q.
  rewrite snd_zip in q.
  rewrite vec2list_map_list2vec in q.
  apply vec2list_injective.
  apply q.
  apply scbwv_exprvars_distinct.
  Qed.

Lemma case_lemma : forall Γ Δ ξ l tc tbranches atypes e alts',
  mapOptionTree ξ (expr2antecedent (ECase Γ Δ ξ l tc tbranches atypes e alts'))
  = ((mapOptionTreeAndFlatten pcb_freevars (mapOptionTree mkProofCaseBranch alts')),,mapOptionTree ξ  (expr2antecedent e)).
  intros.
  simpl.
  Ltac hack := match goal with [ |- ?A,,?B = ?C,,?D ] => assert (A=C) end.
  hack.
  induction alts'.
  simpl.
  destruct a.
  unfold mkProofCaseBranch.
  simpl.
  reflexivity.
  reflexivity.
  simpl.
  rewrite IHalts'1.
  rewrite IHalts'2.
  reflexivity.
  rewrite H.
  reflexivity.
  Qed.


Definition expr2proof  :
  forall Γ Δ ξ τ (e:Expr Γ Δ ξ τ),
    ND Rule [] [Γ > Δ > mapOptionTree ξ (expr2antecedent e) |- [τ]].

  refine (fix expr2proof Γ' Δ' ξ' τ' (exp:Expr Γ' Δ' ξ' τ') {struct exp}
    : ND Rule [] [Γ' > Δ' > mapOptionTree ξ' (expr2antecedent exp) |- [τ']] :=
    match exp as E in Expr Γ Δ ξ τ with
    | EGlobal  Γ Δ ξ t wev                          => let case_EGlobal := tt in _
    | EVar     Γ Δ ξ ev                             => let case_EVar := tt in _
    | ELit     Γ Δ ξ lit lev                        => let case_ELit := tt in _
    | EApp     Γ Δ ξ t1 t2 lev e1 e2                => let case_EApp := tt in 
                                                        (fun e1' e2' => _) (expr2proof _ _ _ _ e1) (expr2proof _ _ _ _ e2)
    | ELam     Γ Δ ξ t1 t2 lev v    e               => let case_ELam := tt in (fun e' => _) (expr2proof _ _ _ _ e)
    | ELet     Γ Δ ξ tv t      v lev ev ebody       => let case_ELet := tt in 
                                                       (fun pf_let pf_body => _) (expr2proof _ _ _ _ ev) (expr2proof _ _ _ _ ebody) 
    | ELetRec  Γ Δ ξ lev t tree branches ebody      =>
      let ξ' := update_ξ ξ lev (leaves tree) in
      let case_ELetRec := tt in  (fun e' subproofs => _) (expr2proof _ _ _ _ ebody) 
        ((fix subproofs Γ'' Δ'' ξ'' lev'' (tree':Tree ??(VV * HaskType Γ'' ★))
        (branches':ELetRecBindings Γ'' Δ'' ξ'' lev'' tree')
        : LetRecSubproofs Γ'' Δ'' ξ'' lev'' tree' branches' :=
        match branches' as B in ELetRecBindings G D X L T return LetRecSubproofs G D X L T B with
          | ELR_nil    Γ Δ ξ lev  => lrsp_nil _ _ _ _
          | ELR_leaf   Γ Δ ξ l v t e => lrsp_leaf Γ Δ ξ l v t e (expr2proof _ _ _ _ e)
          | ELR_branch Γ Δ ξ lev t1 t2 b1 b2 => lrsp_cons _ _ _ _ _ _ _ _ (subproofs _ _ _ _ _ b1) (subproofs _ _ _ _ _ b2)
        end
        ) _ _ _ _ tree branches)
    | EEsc     Γ Δ ξ ec t lev e                     => let case_EEsc    := tt in (fun e' => _) (expr2proof _ _ _ _ e)
    | EBrak    Γ Δ ξ ec t lev e                     => let case_EBrak   := tt in (fun e' => _) (expr2proof _ _ _ _ e)
    | ECast    Γ Δ ξ γ t1 t2 lev      e             => let case_ECast   := tt in (fun e' => _) (expr2proof _ _ _ _ e)
    | ENote    Γ Δ ξ t n e                          => let case_ENote   := tt in (fun e' => _) (expr2proof _ _ _ _ e)
    | ETyLam   Γ Δ ξ κ σ l e                        => let case_ETyLam  := tt in (fun e' => _) (expr2proof _ _ _ _ e)
    | ECoLam   Γ Δ κ σ σ₁ σ₂ ξ l             e      => let case_ECoLam  := tt in (fun e' => _) (expr2proof _ _ _ _ e)
    | ECoApp   Γ Δ κ σ₁ σ₂ σ γ ξ l      e           => let case_ECoApp  := tt in (fun e' => _) (expr2proof _ _ _ _ e)
    | ETyApp   Γ Δ κ σ τ ξ  l    e                  => let case_ETyApp  := tt in (fun e' => _) (expr2proof _ _ _ _ e)
    | ECase    Γ Δ ξ l tc tbranches atypes e alts' => 
      let dcsp :=
        ((fix mkdcsp (alts:
               Tree ??{ scb : StrongCaseBranchWithVVs _ _ tc atypes
                            & Expr (sac_Γ scb Γ)
                                   (sac_Δ scb Γ atypes (weakCK'' Δ))
                                   (scbwv_ξ scb ξ l)
                                   (weakLT' (tbranches@@l)) })
          : ND Rule [] (mapOptionTree (pcb_judg ○ mkProofCaseBranch) alts) :=
        match alts as ALTS return ND Rule [] (mapOptionTree (pcb_judg ○ mkProofCaseBranch) ALTS) with
          | T_Leaf None      => let case_nil := tt in _
          | T_Branch b1 b2   => let case_branch := tt in (fun b1' b2' => _) (mkdcsp b1) (mkdcsp b2)
          | T_Leaf (Some x)  =>
            match x as X return ND Rule [] [(pcb_judg ○ mkProofCaseBranch) X] with
            existT scbx ex =>
            (fun e' => let case_leaf := tt in _) (expr2proof _ _ _ _ ex)
        end
        end) alts')
        in let case_ECase := tt in (fun e' => _) (expr2proof _ _ _ _ e)
    end
  ); clear exp ξ' τ' Γ' Δ' expr2proof; try clear mkdcsp.

    destruct case_EGlobal.
      apply nd_rule.
      simpl.
      destruct t as [t lev].
      apply (RGlobal _ _ _ _ wev).

    destruct case_EVar.
      apply nd_rule.
      unfold mapOptionTree; simpl.
      destruct (ξ ev).
      apply RVar.

    destruct case_ELit.
      apply nd_rule.
      apply RLit.

    destruct case_EApp.
      unfold mapOptionTree; simpl; fold (mapOptionTree ξ).
      eapply nd_comp; [ idtac | eapply nd_rule; apply RApp ].
      eapply nd_comp; [ apply nd_llecnac | idtac ].
      apply nd_prod; auto.
      apply e1'.
      apply e2'.

    destruct case_ELam; intros.
      unfold mapOptionTree; simpl; fold (mapOptionTree ξ).
      eapply nd_comp; [ idtac | eapply nd_rule; apply RLam ].
      set (update_ξ ξ lev ((v,t1)::nil)) as ξ'.
      set (arrangeContextAndWeaken v (expr2antecedent e) Γ Δ [t2 @@ lev] ξ') as pfx.
        apply UND_to_ND in pfx.
        unfold mapOptionTree in pfx; simpl in pfx; fold (mapOptionTree ξ) in pfx.
        unfold ξ' in pfx.
        fold (mapOptionTree (update_ξ ξ lev ((v,t1)::nil))) in pfx.
        rewrite updating_stripped_tree_is_inert in pfx.
        unfold update_ξ in pfx.
        destruct (eqd_dec v v).
        eapply nd_comp; [ idtac | apply pfx ].
        clear pfx.
        apply e'.
        assert False.
        apply n.
        auto.
        inversion H.

    destruct case_ELet; intros; simpl in *.
      eapply nd_comp; [ idtac | eapply nd_rule; eapply RLet ].
      eapply nd_comp; [ apply nd_llecnac | idtac ].
      apply nd_prod; [ idtac | apply pf_let].
      clear pf_let.
      eapply nd_comp; [ apply pf_body | idtac ].
      clear pf_body.
      fold (@mapOptionTree VV).
      fold (mapOptionTree ξ).
      set (update_ξ ξ v ((lev,tv)::nil)) as ξ'.
      set (arrangeContextAndWeaken lev (expr2antecedent ebody) Γ Δ [t@@v] ξ') as n.
      unfold mapOptionTree in n; simpl in n; fold (mapOptionTree ξ') in n.
      unfold ξ' in n.
      rewrite updating_stripped_tree_is_inert in n.
      unfold update_ξ in n.
      destruct (eqd_dec lev lev).
      unfold ξ'.
      unfold update_ξ.
      apply UND_to_ND in n.
      apply n.
      assert False. apply n0; auto. inversion H.

    destruct case_EEsc.
      eapply nd_comp; [ idtac | eapply nd_rule; apply REsc ].
      apply e'.

    destruct case_EBrak; intros.
      eapply nd_comp; [ idtac | eapply nd_rule; apply RBrak ].
      apply e'.

    destruct case_ECast.
      eapply nd_comp; [ idtac | eapply nd_rule; eapply RCast ].
      apply e'.
      auto.

    destruct case_ENote.
      destruct t.
      eapply nd_comp; [ idtac | eapply nd_rule; apply RNote ].
      apply e'.
      auto.

    destruct case_ETyApp; simpl in *; intros.
      eapply nd_comp; [ idtac | eapply nd_rule; apply RAppT ].
      apply e'.
      auto.

    destruct case_ECoLam; simpl in *; intros.
      eapply nd_comp; [ idtac | eapply nd_rule; apply RAbsCo with (κ:=κ) ].
      apply e'.

    destruct case_ECoApp; simpl in *; intros.
      eapply nd_comp; [ idtac | eapply nd_rule; apply (@RAppCo _ _ (mapOptionTree ξ (expr2antecedent e)) _ σ₁ σ₂ σ γ l) ].
      apply e'.
      auto.

    destruct case_ETyLam; intros.
      eapply nd_comp; [ idtac | eapply nd_rule; apply RAbsT ].
      unfold mapOptionTree in e'.
      rewrite mapOptionTree_compose in e'.
      unfold mapOptionTree.
      apply e'.

    destruct case_leaf.
      clear o x alts alts' e.
      eapply nd_comp; [ apply e' | idtac ].
      clear e'.
      set (existT
              (fun scb : StrongCaseBranchWithVVs VV eqd_vv tc atypes =>
               Expr (sac_Γ scb Γ) (sac_Δ scb Γ atypes (weakCK'' Δ))
                 (scbwv_ξ scb ξ l) (weakLT' (tbranches @@  l))) scbx ex) as stuff.
      set (fun q r x1 x2 y1 y2 => @UND_to_ND q r [q >> r > x1 |- y1] [q >> r > x2 |- y2]).
      simpl in n.
      apply n.
      clear n.

      rewrite mapleaves'.
      simpl.
      rewrite <- mapOptionTree_compose.
      rewrite <- updating_stripped_tree_is_inert''' with (l:=l).
      replace (vec2list (scbwv_exprvars scbx)) with (leaves (unleaves (vec2list (scbwv_exprvars scbx)))).
      rewrite <- mapleaves'.
      rewrite vec2list_map_list2vec.
      unfold sac_Γ.      
      rewrite <- (scbwv_coherent scbx l ξ).
      rewrite <- vec2list_map_list2vec.
      rewrite mapleaves'.
      apply arrangeContextAndWeaken''.
      rewrite leaves_unleaves.
      apply (scbwv_exprvars_distinct scbx).
      apply leaves_unleaves.

    destruct case_nil.
      apply nd_id0.

    destruct case_branch.
      simpl; eapply nd_comp; [ apply nd_llecnac | idtac ].
      apply nd_prod.
      apply b1'.
      apply b2'.

    destruct case_ECase.
      rewrite case_lemma.
      eapply nd_comp; [ idtac | eapply nd_rule; eapply RCase ].
      eapply nd_comp; [ apply nd_llecnac | idtac ]; apply nd_prod.
      rewrite <- mapOptionTree_compose.
      apply dcsp.
      apply e'.

    destruct case_ELetRec; intros.
      unfold ξ'0 in *.
      clear ξ'0.
      unfold ξ'1 in *.
      clear ξ'1.
      apply letRecSubproofsToND'.
      apply e'.
      apply subproofs.

  Defined.

End HaskStrongToProof.

