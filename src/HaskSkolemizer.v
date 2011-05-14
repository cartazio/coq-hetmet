(*********************************************************************************************************************************)
(* HaskSkolemizer:                                                                                                               *)
(*                                                                                                                               *)
(*   Skolemizes the portion of a proof which uses judgments at level >0                                                          *)
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
Require Import HaskCoreVars.
Require Import HaskWeakTypes.
Require Import HaskWeakVars.
Require Import HaskLiterals.
Require Import HaskTyCons.
Require Import HaskStrongTypes.
Require Import HaskProof.
Require Import NaturalDeduction.

Require Import HaskStrongTypes.
Require Import HaskStrong.
Require Import HaskProof.
Require Import HaskStrongToProof.
Require Import HaskProofToStrong.
Require Import HaskWeakToStrong.

Open Scope nd_scope.
Set Printing Width 130.

Section HaskSkolemizer.

(*
  Fixpoint debruijn2phoas {κ} (exp: RawHaskType (fun _ => nat) κ) : HaskType TV κ :=
     match exp with
    | TVar    _  x          => x
    | TAll     _ y          => TAll   _  (fun v => debruijn2phoas  (y (TVar v)))
    | TApp   _ _ x y        => TApp      (debruijn2phoas  x) (debruijn2phoas  y)
    | TCon       tc         => TCon      tc
    | TCoerc _ t1 t2 t      => TCoerc    (debruijn2phoas  t1) (debruijn2phoas  t2)   (debruijn2phoas  t)
    | TArrow                => TArrow
    | TCode      v e        => TCode     (debruijn2phoas  v) (debruijn2phoas  e)
    | TyFunApp  tfc kl k lt => TyFunApp tfc kl k (debruijn2phoasyFunApp _ lt)
    end
    with debruijn2phoasyFunApp (lk:list Kind)(exp:@RawHaskTypeList (fun _ => nat) lk) : @HaskTypeList TV lk :=
    match exp in @RawHaskTypeList _ LK return @RawHaskTypeList TV LK with
    | TyFunApp_nil               => TyFunApp_nil
    | TyFunApp_cons  κ kl t rest => TyFunApp_cons _ _ (debruijn2phoas  t) (debruijn2phoasyFunApp _ rest)
    end.
*)
  Definition isNotBrakOrEsc {h}{c} (r:Rule h c) : Prop :=
    match r with
      | RBrak _ _ _ _ _ _ => False
      | REsc  _ _ _ _ _ _ => False
      | _                 => True
    end.

  Fixpoint mkArrows {Γ}(lt:list (HaskType Γ ★))(t:HaskType Γ ★) : HaskType Γ ★ :=
    match lt with
      | nil => t
      | a::b => mkArrows b (a ---> t)
    end.

  Fixpoint unleaves_ {Γ}(t:Tree ??(LeveledHaskType Γ ★))(l:list (HaskType Γ ★)) lev : Tree ??(LeveledHaskType Γ ★) :=
    match l with
      | nil  => t
      | a::b => unleaves_ (t,,[a @@ lev]) b lev
    end.

  (* rules of skolemized proofs *)
  Definition getΓ (j:Judg) := match j with Γ > _ > _ |- _ => Γ end.
  Definition getSuc (j:Judg) : Tree ??(LeveledHaskType (getΓ j) ★) :=
    match j as J return Tree ??(LeveledHaskType (getΓ J) ★) with Γ > _ > _ |- s => s end.
  Fixpoint getjlev {Γ}(tt:Tree ??(LeveledHaskType Γ ★)) : HaskLevel Γ :=
    match tt with
      | T_Leaf None              => nil
      | T_Leaf (Some (_ @@ lev)) => lev
      | T_Branch b1 b2 =>
        match getjlev b1 with
          | nil => getjlev b2
          | lev => lev
        end
    end.

  Fixpoint take_trustme {Γ}
    (n:nat)
    (l:forall TV, InstantiatedTypeEnv TV Γ -> list (RawHaskType TV ★))
    : list (HaskType Γ ★) :=

    match n with
      | 0    => nil
      | S n' => (fun TV ite => match l TV ite with
                | nil  => Prelude_error "impossible"
                | a::b => a
                end)
                ::
                take_trustme n' (fun TV ite => match l TV ite with
                | nil  => Prelude_error "impossible"
                | a::b => b
                end)
    end.
                  
  Definition take_arg_types_as_tree {Γ}(ht:HaskType Γ ★) : Tree ??(HaskType Γ ★ ) :=
    unleaves
    (take_trustme
      (count_arg_types (ht _ (ite_unit _)))
      (fun TV ite => take_arg_types (ht TV ite))).

  Definition drop_arg_types_as_tree {Γ} (ht:HaskType Γ ★) : HaskType Γ ★ :=
    fun TV ite => drop_arg_types (ht TV ite).

  Implicit Arguments take_arg_types_as_tree [[Γ]].
  Implicit Arguments drop_arg_types_as_tree [[Γ]].

  Lemma take_works : forall {Γ}(t1 t2:HaskType Γ ★),
    take_arg_types_as_tree (t1 ---> t2) = [t1],,(take_arg_types_as_tree t2).
    intros.
    unfold take_arg_types_as_tree at 1. 
    simpl.
    admit.
    Qed.

  Lemma drop_works : forall {Γ}(t1 t2:HaskType Γ ★),
    drop_arg_types_as_tree (t1 ---> t2) = (drop_arg_types_as_tree t2).
    intros.
    unfold drop_arg_types_as_tree.
    simpl.
    reflexivity.
    Qed.

  Inductive SRule : Tree ??Judg -> Tree ??Judg -> Type :=
(*  | SFlat  : forall h c (r:Rule h c), isNotBrakOrEsc r -> SRule h c*)
  | SFlat  : forall h c, Rule h c -> SRule h c
  | SBrak  : forall Γ Δ t ec Σ l,
    SRule
    [Γ > Δ > Σ,, (take_arg_types_as_tree t @@@ (ec::l)) |- [ drop_arg_types_as_tree t        @@ (ec::l) ]]
    [Γ > Δ > Σ                                  |- [<[ec |- t]>              @@      l  ]]

  | SEsc   : forall Γ Δ t ec Σ l,
    SRule
    [Γ > Δ > Σ                                  |- [<[ec |- t]>              @@      l  ]]
    [Γ > Δ > Σ,, (take_arg_types_as_tree t @@@ (ec::l)) |- [ drop_arg_types_as_tree t        @@ (ec::l) ]]
    .

  Definition take_arg_types_as_tree' {Γ}(lt:LeveledHaskType Γ ★) :=
    match lt with t @@ l => take_arg_types_as_tree t @@@ l end.

  Definition drop_arg_types_as_tree' {Γ}(lt:LeveledHaskType Γ ★) :=
    match lt with t @@ l => drop_arg_types_as_tree t @@ l end.

  Definition skolemize_judgment (j:Judg) : Judg :=
    match j with
      Γ > Δ > Σ₁ |- Σ₂ =>
        match getjlev Σ₂ with
          | nil => j
          | lev => Γ > Δ > Σ₁,,(mapOptionTreeAndFlatten take_arg_types_as_tree' Σ₂) |- mapOptionTree drop_arg_types_as_tree' Σ₂
        end
    end.

  Definition check_hof : forall {Γ}(t:HaskType Γ ★),
    sumbool
    True
    (take_arg_types_as_tree t = [] /\ drop_arg_types_as_tree t = t).
    intros.
    destruct (eqd_dec (take_arg_types_as_tree t) []);
    destruct (eqd_dec (drop_arg_types_as_tree t) t).
    right; auto.
    left; auto.
    left; auto.
    left; auto.
    Defined.

  Opaque take_arg_types_as_tree.
  Definition skolemize_proof :
    forall  {h}{c},
      ND Rule  h c ->
      ND SRule (mapOptionTree skolemize_judgment h) (mapOptionTree skolemize_judgment c).
    intros.
    eapply nd_map'; [ idtac | apply X ].
    clear h c X.
    intros.

    refine (match X as R in Rule H C with
      | RArrange Γ Δ a b x d           => let case_RArrange := tt      in _
      | RNote    Γ Δ Σ τ l n           => let case_RNote := tt         in _
      | RLit     Γ Δ l     _           => let case_RLit := tt          in _
      | RVar     Γ Δ σ           lev   => let case_RVar := tt          in _
      | RGlobal  Γ Δ σ l wev           => let case_RGlobal := tt       in _
      | RLam     Γ Δ Σ tx te     lev   => let case_RLam := tt          in _
      | RCast    Γ Δ Σ σ τ lev γ       => let case_RCast := tt         in _
      | RAbsT    Γ Δ Σ κ σ lev         => let case_RAbsT := tt         in _
      | RAppT    Γ Δ Σ κ σ τ     lev   => let case_RAppT := tt         in _
      | RAppCo   Γ Δ Σ κ σ₁ σ₂ γ σ lev => let case_RAppCo := tt        in _
      | RAbsCo   Γ Δ Σ κ σ  σ₁ σ₂  lev => let case_RAbsCo := tt        in _
      | RApp     Γ Δ Σ₁ Σ₂ tx te lev   => let case_RApp := tt          in _
      | RLet     Γ Δ Σ₁ Σ₂ σ₁ σ₂ lev   => let case_RLet := tt          in _
      | RJoin    Γ p lri m x q         => let case_RJoin := tt in _
      | RVoid    _ _                   => let case_RVoid := tt   in _
      | RBrak    Γ Δ t ec succ lev           => let case_RBrak := tt         in _
      | REsc     Γ Δ t ec succ lev           => let case_REsc := tt          in _
      | RCase    Γ Δ lev tc Σ avars tbranches alts => let case_RCase := tt         in _
      | RLetRec  Γ Δ lri x y t         => let case_RLetRec := tt       in _
      end); clear X h c.

      destruct case_RArrange.
        simpl.
        destruct (getjlev x).
        apply nd_rule.
        apply SFlat.
        apply RArrange.
        apply d.
        apply nd_rule.
        apply SFlat.
        apply RArrange.
        apply RRight.
        apply d.

      destruct case_RBrak.
        simpl.
        destruct lev; [ idtac | apply (Prelude_error "Brak with nesting depth >1") ].
        apply nd_rule.
        apply SBrak.

      destruct case_REsc.
        simpl.
        destruct lev; [ idtac | apply (Prelude_error "Esc with nesting depth >1") ].
        apply nd_rule.
        apply SEsc.

      destruct case_RNote.
        apply nd_rule.
        apply SFlat.
        simpl.
        destruct l.
        apply RNote.
        apply n.
        apply RNote.
        apply n.

      destruct case_RLit.
        simpl.
        destruct l0.
        apply nd_rule.
        apply SFlat.
        apply RLit.
        set (check_hof (@literalType l Γ)) as hof.
        destruct hof; [ apply (Prelude_error "attempt to use a literal with higher-order type at depth>0") | idtac ].
        destruct a.
        rewrite H.
        rewrite H0.
        simpl.
        eapply nd_comp; [ idtac | eapply nd_rule; eapply SFlat; eapply RArrange; apply RuCanL ].
        apply nd_rule.
        apply SFlat.
        apply RLit.

      destruct case_RVar.
        simpl.
        destruct lev.
        apply nd_rule; apply SFlat; apply RVar.
        set (check_hof σ) as hof.
        destruct hof; [ apply (Prelude_error "attempt to use a variable with higher-order type at depth>0") | idtac ].
        destruct a.
        rewrite H.
        rewrite H0.
        simpl.
        eapply nd_comp; [ idtac | eapply nd_rule; apply SFlat; eapply RArrange; apply RuCanR ].
        apply nd_rule.
        apply SFlat.
        apply RVar.

      destruct case_RGlobal.
        simpl.
        destruct σ.
        apply nd_rule; apply SFlat; apply RGlobal.
        set (check_hof (l wev)) as hof.
        destruct hof; [ apply (Prelude_error "attempt to use a global with higher-order type at depth>0") | idtac ].
        destruct a.
        rewrite H.
        rewrite H0.
        simpl.
        eapply nd_comp; [ idtac | eapply nd_rule; apply SFlat; eapply RArrange; apply RuCanR ].
        apply nd_rule.
        apply SFlat.
        apply RGlobal.

      destruct case_RLam.
        destruct lev.
          apply nd_rule.
          apply SFlat.
          simpl.
          apply RLam.
        simpl.
        rewrite take_works.
        rewrite drop_works.
        apply nd_rule.
          apply SFlat.
          apply RArrange.
          apply RCossa.

      destruct case_RCast.
        simpl.
        destruct lev.
        apply nd_rule.
        apply SFlat.
        apply RCast.
        apply γ.
        apply (Prelude_error "found RCast at level >0").

      destruct case_RJoin.
        simpl.
        destruct (getjlev x).
        destruct (getjlev q).
        apply nd_rule.
        apply SFlat.
        apply RJoin.
        apply (Prelude_error "found RJoin at level >0").
        apply (Prelude_error "found RJoin at level >0").

      destruct case_RApp.
        simpl.
        destruct lev.
        apply nd_rule.
        apply SFlat.
        apply RApp.
        rewrite take_works.
        rewrite drop_works.
        set (check_hof tx) as hof_tx.
        destruct hof_tx; [ apply (Prelude_error "attempt tp apply a higher-order function at depth>0") | idtac ].
        destruct a.
        rewrite H.
        rewrite H0.
        simpl.
        set (@RLet Γ Δ (Σ₂,,take_arg_types_as_tree te @@@ (h :: lev)) Σ₁ (drop_arg_types_as_tree te) tx (h::lev)) as q.
        eapply nd_comp; [ idtac | eapply nd_rule; apply SFlat; eapply RArrange; apply RAssoc ].
        eapply nd_comp; [ idtac | eapply nd_rule; apply SFlat; eapply RArrange; apply RExch ].
        eapply nd_comp; [ idtac | eapply nd_rule; apply SFlat; eapply q ].
        clear q.
        apply nd_prod.
        apply nd_rule.
        apply SFlat.
        apply RArrange.
        apply RCanR.
        eapply nd_comp; [ idtac | eapply nd_rule; apply SFlat; eapply RArrange; apply RAssoc ].
        apply nd_rule; apply SFlat; apply RArrange; apply RLeft; eapply RExch.

      destruct case_RLet.
        simpl.
        destruct lev.
        apply nd_rule.
        apply SFlat.
        apply RLet.
        set (check_hof σ₂) as hof_tx.
        destruct hof_tx; [ apply (Prelude_error "attempt to let-bind a higher-order function at depth>0") | idtac ].
        destruct a.
        rewrite H.
        rewrite H0.
        set (@RLet Γ Δ (Σ₁,,(take_arg_types_as_tree σ₁ @@@ (h::lev))) Σ₂ (drop_arg_types_as_tree σ₁) σ₂ (h::lev)) as q.
        eapply nd_comp; [ idtac | eapply nd_rule; apply SFlat; eapply RArrange; apply RAssoc ].
        eapply nd_comp; [ idtac | eapply nd_rule; apply SFlat; eapply RArrange; eapply RLeft; apply RExch ].
        eapply nd_comp; [ idtac | eapply nd_rule; apply SFlat; eapply RArrange; apply RCossa ].
        eapply nd_comp; [ idtac | eapply nd_rule; apply SFlat; eapply q ].
        clear q.
        apply nd_prod.
        apply nd_rule.
        apply SFlat.
        apply RArrange.
        apply RCanR.
        eapply nd_comp; [ eapply nd_rule; apply SFlat; eapply RArrange; apply RCossa | idtac ].
        eapply nd_comp; [ idtac | eapply nd_rule; apply SFlat; eapply RArrange; apply RAssoc ].
        apply nd_rule.
        apply SFlat.
        apply RArrange.
        apply RLeft.
        eapply RExch.

      destruct case_RVoid.
        simpl.
        apply nd_rule.
        apply SFlat.
        apply RVoid.

      destruct case_RAppT.
        simpl.
        destruct lev; [ apply nd_rule; apply SFlat; apply RAppT | idtac ].
        apply (Prelude_error "RAppT at depth>0").

      destruct case_RAbsT.
        simpl.
        destruct lev; simpl; [ apply nd_rule; apply SFlat; apply (@RAbsT _ _ _ _ _ nil) | idtac ].
        apply (Prelude_error "RAbsT at depth>0").

      destruct case_RAppCo.
        simpl.
        destruct lev; [ apply nd_rule; apply SFlat; apply RAppCo | idtac ].
        apply γ.
        apply (Prelude_error "RAppCo at depth>0").

      destruct case_RAbsCo.
        simpl.
        destruct lev; [ apply nd_rule; apply SFlat; apply RAbsCo | idtac ].
        apply (Prelude_error "RAbsCo at depth>0").

      destruct case_RLetRec.
        simpl.
        destruct t.
        destruct (getjlev (y @@@ nil)).
        apply nd_rule.
        apply SFlat.
        apply (@RLetRec Γ Δ lri x y nil).
        apply (Prelude_error "RLetRec at depth>0").
        apply (Prelude_error "RLetRec at depth>0").

      destruct case_RCase.
        simpl.
        apply (Prelude_error "CASE: BIG FIXME").
        Defined.
  Transparent take_arg_types_as_tree.

End HaskSkolemizer.
