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
Require Import HaskWeakVars.
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
  Definition dropVar (lv:list VV)(v:VV) : ??VV :=
    if fold_left
      (fun a b:bool => if a then true else if b then true else false)
      (map (fun lvv => if eqd_dec lvv v then true else false) lv)
      false
      then None
      else Some v.
  (* later: use mapOptionTreeAndFlatten *)
  Definition stripOutVars (lv:list VV) : Tree ??VV -> Tree ??VV :=
    mapTree (fun x => match x with None => None | Some vt => dropVar lv vt end).

Fixpoint expr2antecedent {Γ'}{Δ'}{ξ'}{τ'}(exp:Expr Γ' Δ' ξ' τ') : Tree ??VV :=
  match exp as E in Expr Γ Δ ξ τ with
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
  | ELR_leaf   Γ Δ ξ lev v e => expr2antecedent e
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

Fixpoint eLetRecTypes {Γ}{Δ}{ξ}{lev}{τ}(elrb:ELetRecBindings Γ Δ ξ lev τ) : Tree ??(LeveledHaskType Γ ★) :=
  match elrb with
  | ELR_nil    Γ Δ ξ lev  => []
  | ELR_leaf   Γ Δ ξ  lev  v e => [ξ v]
  | ELR_branch Γ Δ ξ lev t1 t2 b1 b2 => (eLetRecTypes b1),,(eLetRecTypes b2)
  end.

Fixpoint eLetRecVars {Γ}{Δ}{ξ}{lev}{τ}(elrb:ELetRecBindings Γ Δ ξ lev τ) : Tree ??VV :=
  match elrb with
  | ELR_nil    Γ Δ ξ lev  => []
  | ELR_leaf   Γ Δ ξ  lev  v e => [v]
  | ELR_branch Γ Δ ξ lev t1 t2 b1 b2 => (eLetRecVars b1),,(eLetRecVars b2)
  end.

Fixpoint eLetRecTypesVars {Γ}{Δ}{ξ}{lev}{τ}(elrb:ELetRecBindings Γ Δ ξ lev τ) : Tree ??(VV * LeveledHaskType Γ ★):=
  match elrb with
  | ELR_nil    Γ Δ ξ lev  => []
  | ELR_leaf   Γ Δ ξ  lev  v e => [(v, ξ v)]
  | ELR_branch Γ Δ ξ lev t1 t2 b1 b2 => (eLetRecTypesVars b1),,(eLetRecTypesVars b2)
  end.


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
    rewrite IHtree1.
    rewrite IHtree2.
    reflexivity.
    Qed.



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

  induction ctx; simpl in *.
  
    refine (match a with None => let case_None := tt in _ | Some v' => let case_Some := tt in _ end); simpl in *.
  
        (* nonempty leaf *)
        destruct case_Some.
          unfold stripOutVars in *; simpl.
          unfold dropVar.
          unfold mapOptionTree in *; simpl; fold (mapOptionTree ξ) in *.
          destruct (eqd_dec v v'); simpl in *.

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

Definition arrangeContextAndWeaken'' Γ Δ ξ v : forall ctx z, 
  ND (@URule Γ Δ)
    [Γ >> Δ>(mapOptionTree ξ ctx)                                       |-  z]
    [Γ >> Δ>(mapOptionTree ξ (stripOutVars (leaves v) ctx)),,(mapOptionTree ξ v) |-  z].

  induction v.
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
    set (nd_comp (IHv1 _ _) IHv2') as qq.
    eapply nd_comp.
      apply qq.
      clear qq IHv2' IHv2 IHv1.
        
      assert ((stripOutVars (leaves v2) (stripOutVars (leaves v1) ctx))=(stripOutVars (app (leaves v1) (leaves v2)) ctx)).
        admit.
        rewrite H.
        clear H.

      (* FIXME: this only works because the variables are all distinct, but I need to prove that *)
      assert ((stripOutVars (leaves v2) v1) = v1).
        admit.
        rewrite H.
        clear H.

        apply nd_rule.
        apply RCossa.
    Defined.

Definition update_ξ'' {Γ} ξ tree lev :=
(update_ξ ξ
                  (map (fun x : VV * HaskType Γ ★ => ⟨fst x, snd x @@  lev ⟩)
                     (leaves tree))).

Lemma updating_stripped_tree_is_inert {Γ} (ξ:VV -> LeveledHaskType Γ ★) v tree lev :
      mapOptionTree (update_ξ ξ ((v,lev)::nil)) (stripOutVars (v :: nil) tree)
    = mapOptionTree ξ (stripOutVars (v :: nil) tree).
  induction tree; simpl in *; try reflexivity; auto.

  unfold mapOptionTree in *; simpl; fold (mapOptionTree ξ) in *; fold (mapOptionTree (update_ξ ξ ((v,lev)::nil))) in *.
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
  Qed.



Lemma updating_stripped_tree_is_inert'
  {Γ} lev
  (ξ:VV -> LeveledHaskType Γ ★)
  tree tree2 :
    mapOptionTree (update_ξ'' ξ tree lev) (stripOutVars (leaves (mapOptionTree (@fst _ _) tree)) tree2)
  = mapOptionTree ξ (stripOutVars (leaves (mapOptionTree (@fst _ _) tree)) tree2).
admit.
  Qed.

Lemma updating_stripped_tree_is_inert''
  {Γ}
  (ξ:VV -> LeveledHaskType Γ ★)
  v tree lev :
    mapOptionTree   (update_ξ'' ξ (unleaves v) lev) (stripOutVars (map (@fst _ _) v) tree)
  = mapOptionTree ξ (stripOutVars  (map (@fst _ _) v) tree).
admit.
  Qed.

(*
Lemma updating_stripped_tree_is_inert'''
  {Γ}
  (ξ:VV -> LeveledHaskType Γ)
{T}
  (idx:Tree ??T) (types:ShapedTree (LeveledHaskType Γ) idx)(vars:ShapedTree VV idx) tree
:
    mapOptionTree   (update_ξ''' ξ types vars) (stripOutVars (leaves (unshape vars)) tree)
  = mapOptionTree ξ (stripOutVars (leaves (unshape vars)) tree).
admit.
  Qed.
*)

(* IDEA: use multi-conclusion proofs instead *)
Inductive LetRecSubproofs Γ Δ ξ lev : forall tree, ELetRecBindings Γ Δ ξ lev tree -> Type := 
  | lrsp_nil  : LetRecSubproofs Γ Δ ξ lev [] (ELR_nil _ _ _ _)
  | lrsp_leaf : forall v  e,
    (ND Rule [] [Γ > Δ > mapOptionTree ξ (expr2antecedent e) |- [unlev (ξ v) @@ lev]]) ->
    LetRecSubproofs Γ Δ ξ lev [(v, unlev (ξ v))] (ELR_leaf _ _ _ _ _ e)
  | lrsp_cons : forall t1 t2 b1 b2,
    LetRecSubproofs Γ Δ ξ lev t1 b1 ->
    LetRecSubproofs Γ Δ ξ lev t2 b2 ->
    LetRecSubproofs Γ Δ ξ lev (t1,,t2) (ELR_branch _ _ _ _ _ _ b1 b2).

Lemma cheat1 : forall Γ Δ ξ lev tree (branches:ELetRecBindings Γ Δ ξ lev tree),
  eLetRecTypes branches =
    mapOptionTree  (update_ξ'' ξ tree lev)
    (mapOptionTree (@fst _ _) tree).
  intros.
  induction branches.
  reflexivity.
  simpl.
  unfold update_ξ.
  unfold mapOptionTree; simpl.
admit.
admit.
  Qed.
Lemma cheat2 : forall Γ Δ ξ l tc tbranches atypes e alts',
mapOptionTree ξ (expr2antecedent (ECase Γ Δ ξ l tc tbranches atypes e alts'))
= 
(*
((mapOptionTreeAndFlatten
(fun h => stripOutVars (vec2list (scbwv_exprvars (projT1 h)))
                  (expr2antecedent (projT2 h))) alts'),,(expr2antecedent e)).
*)
((mapOptionTreeAndFlatten pcb_freevars
           (mapOptionTree mkProofCaseBranch alts')),,mapOptionTree ξ  (expr2antecedent e)).
admit.
Qed.
Lemma cheat3 : forall {A}{B}{f:A->B} l, unleaves (map f l) = mapOptionTree f (unleaves l).
  admit.
  Qed.
Lemma cheat4 : forall {A}(t:list A), leaves (unleaves t) = t.
admit.
Qed.

Lemma letRecSubproofsToND Γ Δ ξ lev tree branches
    : LetRecSubproofs Γ Δ ξ lev tree branches ->
    ND Rule []
    [ Γ > Δ >
      mapOptionTree ξ (eLetRecContext branches)
      |-
  eLetRecTypes branches
    ].
  intro X.
  induction X; intros; simpl in *.
    apply nd_rule.
      apply REmptyGroup.
    set (ξ v) as q in *.
      destruct q.
      simpl in *.
      assert (h0=lev).
        admit.
        rewrite H.
      apply n.
    eapply nd_comp; [ idtac | eapply nd_rule; apply RBindingGroup ].
    eapply nd_comp; [ apply nd_llecnac | idtac ].
    apply nd_prod; auto.
  Defined.


Lemma update_twice_useless : forall Γ (ξ:VV -> LeveledHaskType Γ ★) tree z lev,
  mapOptionTree (@update_ξ'' Γ ξ tree lev) z = mapOptionTree (update_ξ'' (update_ξ'' ξ tree lev) tree lev) z.
admit.
  Qed.



Lemma letRecSubproofsToND' Γ Δ ξ lev τ tree  :
    forall branches body,
    ND Rule [] [Γ > Δ > mapOptionTree (update_ξ'' ξ tree lev) (expr2antecedent body) |- [τ @@ lev]] -> 
    LetRecSubproofs Γ Δ (update_ξ'' ξ tree lev) lev tree branches ->
    ND Rule [] [Γ > Δ > mapOptionTree ξ (expr2antecedent (@ELetRec VV _ Γ Δ ξ lev τ tree branches body)) |- [τ @@ lev]].

  (* NOTE: how we interpret stuff here affects the order-of-side-effects *)
  simpl.
  intro branches.
  intro body.
  intro pf.
  intro lrsp.
  set ((update_ξ ξ
           (map (fun x : VV * HaskType Γ ★ => ⟨fst x, snd x @@  lev ⟩)
              (leaves tree)))) as ξ' in *.
  set ((stripOutVars (leaves (mapOptionTree (@fst _ _) tree)) (eLetRecContext branches))) as ctx.
  set (mapOptionTree (@fst _ _) tree) as pctx.
  set (mapOptionTree ξ' pctx) as passback.
  set (fun a b => @RLetRec Γ Δ a b passback) as z.
  eapply nd_comp; [ idtac | eapply nd_rule; apply z ].
  clear z.

  set (@arrangeContextAndWeaken''  Γ Δ ξ' pctx (expr2antecedent body,,eLetRecContext branches)) as q'.
  unfold passback in *; clear passback.
  unfold pctx in *; clear pctx.
  eapply UND_to_ND in q'.

  unfold ξ' in *.
  set (@updating_stripped_tree_is_inert') as zz.
  unfold update_ξ'' in *.
  rewrite zz in q'.
  clear zz.
  clear ξ'.
  simpl in q'.

  eapply nd_comp; [ idtac | apply q' ].
  clear q'.
  unfold mapOptionTree. simpl. fold (mapOptionTree (update_ξ'' ξ tree lev)).

  simpl.

  set (letRecSubproofsToND _ _ _ _ _ branches lrsp) as q.

    eapply nd_comp; [ idtac | eapply nd_rule; apply RBindingGroup ].
    eapply nd_comp; [ apply nd_llecnac | idtac ].
    apply nd_prod; auto.
    rewrite cheat1 in q.
    set (@update_twice_useless Γ ξ tree ((mapOptionTree (@fst _ _) tree)) lev) as zz.
    unfold update_ξ'' in *.
    rewrite <- zz in q.
    apply q.
  Defined.


Lemma updating_stripped_tree_is_inert''' : forall Γ tc ξ l t atypes x,
         mapOptionTree (scbwv_ξ(Γ:=Γ)(tc:=tc)(atypes:=atypes) x ξ l)
           (stripOutVars (vec2list (scbwv_exprvars x)) t)
             =
         mapOptionTree (weakLT' ○ ξ)
           (stripOutVars (vec2list (scbwv_exprvars x)) t).
  admit.
  Qed.


Lemma updating_stripped_tree_is_inert'''' : forall Γ Δ ξ l tc atypes tbranches 
(x:StrongCaseBranchWithVVs(Γ:=Γ) VV eqd_vv tc atypes)
(e0:Expr (sac_Γ x Γ) (sac_Δ x Γ atypes (weakCK'' Δ)) 
    (scbwv_ξ x ξ l) (weakT' tbranches @@  weakL' l)) ,
mapOptionTree (weakLT' ○ ξ)
        (stripOutVars (vec2list (scbwv_exprvars x)) (expr2antecedent e0)),,
unleaves (vec2list (sac_types x Γ atypes)) @@@ weakL' l
=
mapOptionTree (weakLT' ○ ξ)
        (stripOutVars (vec2list (scbwv_exprvars x)) (expr2antecedent e0)),,
         mapOptionTree
           (update_ξ (weakLT' ○ ξ)
              (vec2list
                 (vec_map
                    (fun
                       x0 : VV *
                            HaskType
                              (app (vec2list (sac_ekinds x)) Γ)
                              ★ => ⟨fst x0, snd x0 @@  weakL' l ⟩)
                    (vec_zip (scbwv_exprvars x)
                       (sac_types x Γ atypes)))))
           (unleaves (vec2list (scbwv_exprvars x)))
.
admit.
Qed.




Definition expr2proof  :
  forall Γ Δ ξ τ (e:Expr Γ Δ ξ τ),
    ND Rule [] [Γ > Δ > mapOptionTree ξ (expr2antecedent e) |- [τ]].

  refine (fix expr2proof Γ' Δ' ξ' τ' (exp:Expr Γ' Δ' ξ' τ') {struct exp}
    : ND Rule [] [Γ' > Δ' > mapOptionTree ξ' (expr2antecedent exp) |- [τ']] :=
    match exp as E in Expr Γ Δ ξ τ with
    | EVar     Γ Δ ξ ev                             => let case_EVar := tt in _
    | ELit     Γ Δ ξ lit lev                        => let case_ELit := tt in _
    | EApp     Γ Δ ξ t1 t2 lev e1 e2                => let case_EApp := tt in 
                                                        (fun e1' e2' => _) (expr2proof _ _ _ _ e1) (expr2proof _ _ _ _ e2)
    | ELam     Γ Δ ξ t1 t2 lev v    e               => let case_ELam := tt in (fun e' => _) (expr2proof _ _ _ _ e)
    | ELet     Γ Δ ξ tv t      v lev ev ebody       => let case_ELet := tt in 
                                                       (fun pf_let pf_body => _) (expr2proof _ _ _ _ ev) (expr2proof _ _ _ _ ebody) 
    | ELetRec  Γ Δ ξ lev t tree branches ebody      =>
      let ξ' := update_ξ'' ξ tree lev in
      let case_ELetRec := tt in  (fun e' subproofs => _) (expr2proof _ _ _ _ ebody) 
((fix subproofs Γ'' Δ'' ξ'' lev'' (tree':Tree ??(VV * HaskType Γ'' ★))
        (branches':ELetRecBindings Γ'' Δ'' ξ'' lev'' tree')
        : LetRecSubproofs Γ'' Δ'' ξ'' lev'' tree' branches' :=
        match branches' as B in ELetRecBindings G D X L T return LetRecSubproofs G D X L T B with
          | ELR_nil    Γ Δ ξ lev  => lrsp_nil _ _ _ _
          | ELR_leaf   Γ Δ ξ l v e => lrsp_leaf Γ Δ ξ l v e (expr2proof _ _ _ _ e)
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
          | T_Leaf None       => let case_nil := tt in _
          | T_Leaf (Some x)   => (fun ecb' => let case_leaf := tt in _) (expr2proof _ _ _ _ (projT2 x))
          | T_Branch b1 b2   => let case_branch := tt in (fun b1' b2' => _) (mkdcsp b1) (mkdcsp b2)
        end) alts')
        in let case_ECase := tt in (fun e' => _) (expr2proof _ _ _ _ e)
    end
); clear exp ξ' τ' Γ' Δ' expr2proof; try clear mkdcsp.

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
      set (update_ξ ξ ((v,t1@@lev)::nil)) as ξ'.
      set (arrangeContextAndWeaken v (expr2antecedent e) Γ Δ [t2 @@ lev] ξ') as pfx.
        apply UND_to_ND in pfx.
        unfold mapOptionTree in pfx; simpl in pfx; fold (mapOptionTree ξ) in pfx.
        unfold ξ' in pfx.
        fold (mapOptionTree (update_ξ ξ ((v,(t1@@lev))::nil))) in pfx.
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
      set (update_ξ ξ ((lev,(tv @@ v))::nil)) as ξ'.
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
      unfold pcb_judg.
      simpl.
      repeat rewrite <- mapOptionTree_compose in *.
      set (nd_comp ecb' (UND_to_ND _ _ _ _ (@arrangeContextAndWeaken'' _ _ _
        (unleaves (vec2list (scbwv_exprvars (projT1 x))))
      (*(unleaves (vec2list (sac_types (projT1 x) Γ atypes)))*)
        _ _
      ))) as q.
      rewrite cheat4 in q.
      rewrite cheat3.
      unfold weakCK'' in q.
      simpl in q.
      rewrite (updating_stripped_tree_is_inert''' Γ tc ξ l _ atypes  (projT1 x)) in q.
      Ltac cheater Q :=
       match goal with
        [ Q:?Y |- ?Z ] =>
         assert (Y=Z) end.
      cheater q.
      admit.
      rewrite <- H.
      clear H.
      apply q.

    destruct case_nil.
      apply nd_id0.

    destruct case_branch.
      simpl; eapply nd_comp; [ apply nd_llecnac | idtac ].
      apply nd_prod.
      apply b1'.
      apply b2'.

    destruct case_ECase.
      rewrite cheat2.
      eapply nd_comp; [ idtac | eapply nd_rule; eapply RCase ].
      eapply nd_comp; [ apply nd_llecnac | idtac ]; apply nd_prod.
      rewrite <- mapOptionTree_compose.
      apply dcsp.
      apply e'.

    destruct case_ELetRec; simpl in *; intros.
      set (@letRecSubproofsToND') as q.
      simpl in q.
      apply q.
      clear q.
      apply e'.
      apply subproofs.

  Defined.

End HaskStrongToProof.

(*

(* Figure 7, production "decl"; actually not used in this formalization *)
Inductive Decl :=.
| DeclDataType     : forall tc:TyCon,      (forall dc:DataCon tc, DataConDecl dc)      -> Decl
| DeclTypeFunction : forall n t l,         TypeFunctionDecl n t l                      -> Decl
| DeclAxiom        : forall n ccon vk TV,  @AxiomDecl        n ccon vk  TV             -> Decl.

(* Figure 1, production "pgm" *)
Inductive Pgm Γ Δ :=
  mkPgm : forall (τ:HaskType Γ), list Decl -> ND Rule [] [Γ>Δ> [] |- [τ @@nil]] -> Pgm Γ Δ.
*)

