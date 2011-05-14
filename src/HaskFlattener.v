(*********************************************************************************************************************************)
(* HaskFlattener:                                                                                                                *)
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

Require Import HaskSkolemizer.

Open Scope nd_scope.
Set Printing Width 130.

(*
 *  The flattening transformation.  Currently only TWO-level languages are
 *  supported, and the level-1 sublanguage is rather limited.
 *
 *  This file abuses terminology pretty badly.  For purposes of this file,
 *  "PCF" means "the level-1 sublanguage" and "FC" (aka System FC) means 
 *  the whole language (level-0 language including bracketed level-1 terms)
 *)
Section HaskFlattener.

  Definition getlev {Γ}{κ}(lht:LeveledHaskType Γ κ) : HaskLevel Γ :=
    match lht with t @@ l => l end.

  Definition arrange :
    forall {T} (Σ:Tree ??T) (f:T -> bool),
      Arrange Σ (dropT (mkFlags (liftBoolFunc false f) Σ),,( (dropT (mkFlags (liftBoolFunc false (bnot ○ f)) Σ)))).
    intros.
    induction Σ.
      simpl.
      destruct a.
      simpl.
      destruct (f t); simpl.
      apply RuCanL.
      apply RuCanR.
      simpl.
      apply RuCanL.
      simpl in *.
      eapply RComp; [ idtac | apply arrangeSwapMiddle ].
      eapply RComp.
      eapply RLeft.
      apply IHΣ2.
      eapply RRight.
      apply IHΣ1.
      Defined.

  Definition arrange' :
    forall {T} (Σ:Tree ??T) (f:T -> bool),
      Arrange (dropT (mkFlags (liftBoolFunc false f) Σ),,( (dropT (mkFlags (liftBoolFunc false (bnot ○ f)) Σ)))) Σ.
    intros.
    induction Σ.
      simpl.
      destruct a.
      simpl.
      destruct (f t); simpl.
      apply RCanL.
      apply RCanR.
      simpl.
      apply RCanL.
      simpl in *.
      eapply RComp; [ apply arrangeSwapMiddle | idtac ].
      eapply RComp.
      eapply RLeft.
      apply IHΣ2.
      eapply RRight.
      apply IHΣ1.
      Defined.

  Ltac eqd_dec_refl' :=
    match goal with
      | [ |- context[@eqd_dec ?T ?V ?X ?X] ] =>
        destruct (@eqd_dec T V X X) as [eqd_dec1 | eqd_dec2];
          [ clear eqd_dec1 | set (eqd_dec2 (refl_equal _)) as eqd_dec2'; inversion eqd_dec2' ]
  end.

  Definition v2t {Γ}(ec:HaskTyVar Γ ECKind) : HaskType Γ ECKind := fun TV ite => TVar (ec TV ite).

  Definition levelMatch {Γ}(lev:HaskLevel Γ) : LeveledHaskType Γ ★ -> bool :=
    fun t => match t with ttype@@tlev => if eqd_dec tlev lev then true else false end.

  (* In a tree of types, replace any type at depth "lev" or greater None *)
  Definition mkDropFlags {Γ}(lev:HaskLevel Γ)(tt:Tree ??(LeveledHaskType Γ ★)) : TreeFlags tt :=
    mkFlags (liftBoolFunc false (levelMatch lev)) tt.

  Definition drop_lev {Γ}(lev:HaskLevel Γ)(tt:Tree ??(LeveledHaskType Γ ★)) : Tree ??(LeveledHaskType Γ ★) :=
    dropT (mkDropFlags lev tt).

  (* The opposite: replace any type which is NOT at level "lev" with None *)
  Definition mkTakeFlags {Γ}(lev:HaskLevel Γ)(tt:Tree ??(LeveledHaskType Γ ★)) : TreeFlags tt :=
    mkFlags (liftBoolFunc true (bnot ○ levelMatch lev)) tt.

  Definition take_lev {Γ}(lev:HaskLevel Γ)(tt:Tree ??(LeveledHaskType Γ ★)) : Tree ??(LeveledHaskType Γ ★) :=
    dropT (mkTakeFlags lev tt).
(*
    mapOptionTree (fun x => flatten_type (unlev x))
    (maybeTree (takeT tt (mkFlags (
      fun t => match t with
                 | Some (ttype @@ tlev) => if eqd_dec tlev lev then true else false
                 | _                    => true
               end
    ) tt))).

  Definition maybeTree {T}(t:??(Tree ??T)) : Tree ??T :=
    match t with
      | None   => []
      | Some x => x
    end.
*)

  Lemma drop_lev_lemma : forall Γ (lev:HaskLevel Γ) x, drop_lev lev [x @@  lev] = [].
    intros; simpl.
    Opaque eqd_dec.
    unfold drop_lev.
    simpl.
    unfold mkDropFlags.
    simpl.
    Transparent eqd_dec.
    eqd_dec_refl'.
    auto.
    Qed.

  Lemma drop_lev_lemma_s : forall Γ (lev:HaskLevel Γ) ec x, drop_lev (ec::lev) [x @@  (ec :: lev)] = [].
    intros; simpl.
    Opaque eqd_dec.
    unfold drop_lev.
    unfold mkDropFlags.
    simpl.
    Transparent eqd_dec.
    eqd_dec_refl'.
    auto.
    Qed.

  Lemma take_lemma : forall Γ (lev:HaskLevel Γ) x, take_lev lev [x @@  lev] = [x @@ lev].
    intros; simpl.
    Opaque eqd_dec.
    unfold take_lev.
    unfold mkTakeFlags.
    simpl.
    Transparent eqd_dec.
    eqd_dec_refl'.
    auto.
    Qed.

  Lemma take_lemma' : forall Γ (lev:HaskLevel Γ) x, take_lev lev (x @@@ lev) = x @@@ lev.
    intros.
    induction x.
    destruct a; simpl; try reflexivity.
    apply take_lemma.
    simpl.
    rewrite <- IHx1 at 2.
    rewrite <- IHx2 at 2.
    reflexivity.
    Qed.
(*
  Lemma drop_lev_lemma' : forall Γ (lev:HaskLevel Γ) x, drop_lev lev (x @@@ lev) = [].
    intros.
    induction x.
    destruct a; simpl; try reflexivity.
    apply drop_lev_lemma.
    simpl.
    change (@drop_lev _ lev (x1 @@@ lev ,, x2 @@@ lev))
      with ((@drop_lev _ lev (x1 @@@ lev)) ,, (@drop_lev _ lev (x2 @@@ lev))).
    simpl.
    rewrite IHx1.
    rewrite IHx2.
    reflexivity.
    Qed.
*)
  Ltac drop_simplify :=
    match goal with
      | [ |- context[@drop_lev ?G ?L [ ?X @@ ?L ] ] ] =>
        rewrite (drop_lev_lemma G L X)
(*
      | [ |- context[@drop_lev ?G ?L [ ?X @@@ ?L ] ] ] =>
        rewrite (drop_lev_lemma' G L X)
*)
      | [ |- context[@drop_lev ?G (?E :: ?L) [ ?X @@ (?E :: ?L) ] ] ] =>
        rewrite (drop_lev_lemma_s G L E X)
      | [ |- context[@drop_lev ?G ?N (?A,,?B)] ] =>
      change (@drop_lev G N (A,,B)) with ((@drop_lev G N A),,(@drop_lev G N B))
      | [ |- context[@drop_lev ?G ?N (T_Leaf None)] ] =>
      change (@drop_lev G N (T_Leaf (@None (LeveledHaskType G ★)))) with (T_Leaf (@None (LeveledHaskType G ★)))
    end.

  Ltac take_simplify :=
    match goal with
      | [ |- context[@take_lev ?G ?L [ ?X @@ ?L ] ] ] =>
        rewrite (take_lemma G L X)
      | [ |- context[@take_lev ?G ?L [ ?X @@@ ?L ] ] ] =>
        rewrite (take_lemma' G L X)
      | [ |- context[@take_lev ?G ?N (?A,,?B)] ] =>
      change (@take_lev G N (A,,B)) with ((@take_lev G N A),,(@take_lev G N B))
      | [ |- context[@take_lev ?G ?N (T_Leaf None)] ] =>
      change (@take_lev G N (T_Leaf (@None (LeveledHaskType G ★)))) with (T_Leaf (@None (LeveledHaskType G ★)))
    end.


  (*******************************************************************************)


  Context (hetmet_flatten : WeakExprVar).
  Context (hetmet_unflatten : WeakExprVar).
  Context (hetmet_id      : WeakExprVar).
  Context {unitTy : forall TV, RawHaskType TV ECKind  -> RawHaskType TV ★                                          }.
  Context {prodTy : forall TV, RawHaskType TV ECKind  -> RawHaskType TV ★  -> RawHaskType TV ★ -> RawHaskType TV ★ }.
  Context {gaTy   : forall TV, RawHaskType TV ECKind  -> RawHaskType TV ★ -> RawHaskType TV ★  -> RawHaskType TV ★ }.

  Definition ga_mk_tree' {TV}(ec:RawHaskType TV ECKind)(tr:Tree ??(RawHaskType TV ★)) : RawHaskType TV ★ :=
    reduceTree (unitTy TV ec) (prodTy TV ec) tr.

  Definition ga_mk_tree {Γ}(ec:HaskType Γ ECKind)(tr:Tree ??(HaskType Γ ★)) : HaskType Γ ★ :=
    fun TV ite => ga_mk_tree' (ec TV ite) (mapOptionTree (fun x => x TV ite) tr).

  Definition ga_mk_raw {TV}(ec:RawHaskType TV ECKind)(ant suc:Tree ??(RawHaskType TV ★)) : RawHaskType TV ★ :=
    gaTy TV ec
    (ga_mk_tree' ec ant)
    (ga_mk_tree' ec suc).

  Definition ga_mk {Γ}(ec:HaskType Γ ECKind)(ant suc:Tree ??(HaskType Γ ★)) : HaskType Γ ★ :=
    fun TV ite => gaTy TV (ec TV ite) (ga_mk_tree ec ant TV ite) (ga_mk_tree ec suc TV ite).

  (*
   *  The story:
   *    - code types <[t]>@c                                                become garrows  c () t 
   *    - free variables of type t at a level lev deeper than the succedent become garrows  c () t
   *    - free variables at the level of the succedent become 
   *)
  Fixpoint flatten_rawtype {TV}{κ}(exp: RawHaskType TV κ) : RawHaskType TV κ :=
    match exp with
    | TVar    _  x          => TVar x
    | TAll     _ y          => TAll   _  (fun v => flatten_rawtype (y v))
    | TApp   _ _ x y        => TApp      (flatten_rawtype x) (flatten_rawtype y)
    | TCon       tc         => TCon      tc
    | TCoerc _ t1 t2 t      => TCoerc    (flatten_rawtype t1) (flatten_rawtype t2) (flatten_rawtype t)
    | TArrow                => TArrow
    | TCode     ec e        => let e' := flatten_rawtype e
                               in  ga_mk_raw ec (unleaves' (take_arg_types e')) [drop_arg_types e']
    | TyFunApp  tfc kl k lt => TyFunApp tfc kl k (flatten_rawtype_list _ lt)
    end
    with flatten_rawtype_list {TV}(lk:list Kind)(exp:@RawHaskTypeList TV lk) : @RawHaskTypeList TV lk :=
    match exp in @RawHaskTypeList _ LK return @RawHaskTypeList TV LK with
    | TyFunApp_nil               => TyFunApp_nil
    | TyFunApp_cons  κ kl t rest => TyFunApp_cons _ _ (flatten_rawtype t) (flatten_rawtype_list _ rest)
    end.

  Definition flatten_type {Γ}{κ}(ht:HaskType Γ κ) : HaskType Γ κ :=
    fun TV ite => flatten_rawtype (ht TV ite).

  Fixpoint levels_to_tcode {Γ}(ht:HaskType Γ ★)(lev:HaskLevel Γ) : HaskType Γ ★ :=
    match lev with
      | nil      => flatten_type ht
      | ec::lev' => @ga_mk _ (v2t ec) [] [levels_to_tcode ht lev']
    end.

  Definition flatten_leveled_type {Γ}(ht:LeveledHaskType Γ ★) : LeveledHaskType Γ ★ :=
    levels_to_tcode (unlev ht) (getlev ht) @@ nil.

  (* AXIOMS *)

  Axiom literal_types_unchanged : forall Γ l, flatten_type (literalType l) = literalType(Γ:=Γ) l.

  Axiom flatten_coercion : forall Γ Δ κ (σ τ:HaskType Γ κ) (γ:HaskCoercion Γ Δ (σ ∼∼∼ τ)),
    HaskCoercion Γ Δ (flatten_type σ ∼∼∼ flatten_type τ).

  Axiom flatten_commutes_with_substT :
    forall  κ Γ (Δ:CoercionEnv Γ) (σ:∀ TV, InstantiatedTypeEnv TV Γ → TV κ → RawHaskType TV ★) (τ:HaskType Γ κ),
    flatten_type  (substT σ τ) = substT (fun TV ite v => flatten_rawtype  (σ TV ite v))
      (flatten_type  τ).

  Axiom flatten_commutes_with_HaskTAll :
    forall  κ Γ (Δ:CoercionEnv Γ) (σ:∀ TV, InstantiatedTypeEnv TV Γ → TV κ → RawHaskType TV ★),
    flatten_type  (HaskTAll κ σ) = HaskTAll κ (fun TV ite v => flatten_rawtype (σ TV ite v)).

  Axiom flatten_commutes_with_HaskTApp :
    forall  κ Γ (Δ:CoercionEnv Γ) (σ:∀ TV, InstantiatedTypeEnv TV Γ → TV κ → RawHaskType TV ★),
    flatten_type  (HaskTApp (weakF σ) (FreshHaskTyVar κ)) =
    HaskTApp (weakF (fun TV ite v => flatten_rawtype  (σ TV ite v))) (FreshHaskTyVar κ).

  Axiom flatten_commutes_with_weakLT : forall (Γ:TypeEnv) κ  t,
    flatten_leveled_type  (weakLT(Γ:=Γ)(κ:=κ) t) = weakLT(Γ:=Γ)(κ:=κ) (flatten_leveled_type  t).

  Axiom globals_do_not_have_code_types : forall (Γ:TypeEnv) (g:Global Γ) v,
    flatten_type (g v) = g v.

  (* This tries to assign a single level to the entire succedent of a judgment.  If the succedent has types from different
   * levels (should not happen) it just picks one; if the succedent has no non-None leaves (also should not happen) it
   * picks nil *)
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

  (* "n" is the maximum depth remaining AFTER flattening *)
  Definition flatten_judgment (j:Judg) :=
    match j as J return Judg with
      Γ > Δ > ant |- suc =>
        match getjlev suc with
          | nil        => Γ > Δ > mapOptionTree flatten_leveled_type ant
                               |- mapOptionTree flatten_leveled_type suc

          | (ec::lev') => Γ > Δ > mapOptionTree flatten_leveled_type (drop_lev (ec::lev') ant)
                               |- [ga_mk (v2t ec)
                                         (mapOptionTree (flatten_type ○ unlev) (take_lev (ec::lev') ant))
                                         (mapOptionTree (flatten_type ○ unlev)                      suc )
                                         @@ nil]  (* we know the level of all of suc *)
        end
    end.

  Class garrow :=
  { ga_id        : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec a a @@ l] ]
  ; ga_cancelr   : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec (a,,[]) a @@ l] ]
  ; ga_cancell   : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec ([],,a) a @@ l] ]
  ; ga_uncancelr : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec a (a,,[]) @@ l] ]
  ; ga_uncancell : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec a ([],,a) @@ l] ]
  ; ga_assoc     : ∀ Γ Δ ec l a b c, ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec ((a,,b),,c) (a,,(b,,c)) @@ l] ]
  ; ga_unassoc   : ∀ Γ Δ ec l a b c, ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec (a,,(b,,c)) ((a,,b),,c) @@ l] ]
  ; ga_swap      : ∀ Γ Δ ec l a b  , ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec (a,,b) (b,,a) @@ l] ]
  ; ga_drop      : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec a [] @@ l] ]
  ; ga_copy      : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec a (a,,a) @@ l] ]
  ; ga_first     : ∀ Γ Δ ec l a b x, ND Rule [] [Γ > Δ >      [@ga_mk Γ ec a b @@ l] |- [@ga_mk Γ ec (a,,x) (b,,x) @@ l] ]
  ; ga_second    : ∀ Γ Δ ec l a b x, ND Rule [] [Γ > Δ >      [@ga_mk Γ ec a b @@ l] |- [@ga_mk Γ ec (x,,a) (x,,b) @@ l] ]
  ; ga_lit       : ∀ Γ Δ ec l lit  , ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec [] [literalType lit] @@ l] ]
  ; ga_curry     : ∀ Γ Δ ec l a b c, ND Rule [] [Γ > Δ > [@ga_mk Γ ec (a,,[b]) [c] @@ l] |- [@ga_mk Γ ec a [b ---> c] @@ l] ]
  ; ga_comp      : ∀ Γ Δ ec l a b c, ND Rule [] [Γ > Δ > [@ga_mk Γ ec a b @@ l],,[@ga_mk Γ ec b c @@ l] |- [@ga_mk Γ ec a c @@ l] ] 
  ; ga_apply     : ∀ Γ Δ ec l a a' b c,
                 ND Rule [] [Γ > Δ > [@ga_mk Γ ec a [b ---> c] @@ l],,[@ga_mk Γ ec a' [b] @@ l] |- [@ga_mk Γ ec (a,,a') [c] @@ l] ]
  ; ga_kappa     : ∀ Γ Δ ec l a b Σ, ND Rule
  [Γ > Δ > Σ,,[@ga_mk Γ ec [] a @@ l] |- [@ga_mk Γ ec [] b @@ l] ]
  [Γ > Δ > Σ          |- [@ga_mk Γ ec a  b @@ l] ]
  }.
  Context `(gar:garrow).

  Notation "a ~~~~> b" := (@ga_mk _ _ a b) (at level 20).

  Definition boost : forall Γ Δ ant x y {lev},
    ND Rule []                          [ Γ > Δ > [x@@lev] |- [y@@lev] ] ->
    ND Rule [ Γ > Δ > ant |- [x@@lev] ] [ Γ > Δ > ant      |- [y@@lev] ].
    intros.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply RCanL ].
    eapply nd_comp; [ idtac | eapply nd_rule; apply (@RLet Γ Δ [] ant y x lev) ].
    eapply nd_comp; [ apply nd_rlecnac | idtac ].
    apply nd_prod.
    apply nd_id.
    eapply nd_comp.
      apply X.
      eapply nd_rule.
      eapply RArrange.
      apply RuCanL.
      Defined.

  Definition postcompose' : ∀ Γ Δ ec lev a b c Σ,
     ND Rule [] [ Γ > Δ > Σ                        |- [@ga_mk Γ ec a b @@ lev] ] ->
     ND Rule [] [ Γ > Δ > Σ,,[@ga_mk Γ ec b c @@ lev] |- [@ga_mk Γ ec a c @@ lev] ].
     intros.
     eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply RExch ].
     eapply nd_comp; [ idtac
       | eapply nd_rule; apply (@RLet Γ Δ [@ga_mk _ ec b c @@lev] Σ (@ga_mk _ ec a c) (@ga_mk _ ec a b) lev) ].
     eapply nd_comp; [ apply nd_llecnac | idtac ].
     apply nd_prod.
     apply X.
     eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; apply RExch ].
     apply ga_comp.
     Defined.

  Definition precompose Γ Δ ec : forall a x y z lev,
    ND Rule
      [ Γ > Δ > a                           |- [@ga_mk _ ec y z @@ lev] ]
      [ Γ > Δ > a,,[@ga_mk _ ec x y @@ lev] |- [@ga_mk _ ec x z @@ lev] ].
    intros.
    eapply nd_comp.
    apply nd_rlecnac.
    eapply nd_comp.
    eapply nd_prod.
    apply nd_id.
    eapply ga_comp.

    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; apply RExch ].

    apply nd_rule.
    apply RLet.
    Defined.

  Definition precompose' : ∀ Γ Δ ec lev a b c Σ,
     ND Rule [] [ Γ > Δ > Σ                           |- [@ga_mk Γ ec b c @@ lev] ] ->
     ND Rule [] [ Γ > Δ > Σ,,[@ga_mk Γ ec a b @@ lev] |- [@ga_mk Γ ec a c @@ lev] ].
     intros.
     eapply nd_comp.
     apply X.
     apply precompose.
     Defined.

  Definition postcompose : ∀ Γ Δ ec lev a b c,
     ND Rule [] [ Γ > Δ > []                    |- [@ga_mk Γ ec a b @@ lev] ] ->
     ND Rule [] [ Γ > Δ > [@ga_mk Γ ec b c @@ lev] |- [@ga_mk Γ ec a c @@ lev] ].
     intros.
     eapply nd_comp.
     apply postcompose'.
     apply X.
     apply nd_rule.
     apply RArrange.
     apply RCanL.
     Defined.

  Definition firstify : ∀ Γ Δ ec lev a b c Σ,
    ND Rule [] [ Γ > Δ > Σ                     |- [@ga_mk Γ ec a b @@ lev] ] ->
    ND Rule [] [ Γ > Δ > Σ                    |- [@ga_mk Γ ec (a,,c) (b,,c) @@ lev] ].
    intros.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply RCanL ].
    eapply nd_comp; [ idtac | eapply nd_rule; apply RLet ].
    eapply nd_comp; [ apply nd_llecnac | idtac ].
    apply nd_prod.
    apply X.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply RuCanL ].
    apply ga_first.
    Defined.

  Definition secondify : ∀ Γ Δ ec lev a b c Σ,
     ND Rule [] [ Γ > Δ > Σ                    |- [@ga_mk Γ ec a b @@ lev] ] ->
     ND Rule [] [ Γ > Δ > Σ                    |- [@ga_mk Γ ec (c,,a) (c,,b) @@ lev] ].
    intros.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply RCanL ].
    eapply nd_comp; [ idtac | eapply nd_rule; apply RLet ].
    eapply nd_comp; [ apply nd_llecnac | idtac ].
    apply nd_prod.
    apply X.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply RuCanL ].
    apply ga_second.
    Defined.

  Lemma ga_unkappa     : ∀ Γ Δ ec l z a b Σ,
    ND Rule
    [Γ > Δ > Σ                         |- [@ga_mk Γ ec a b @@ l] ] 
    [Γ > Δ > Σ,,[@ga_mk Γ ec z a @@ l] |- [@ga_mk Γ ec z b @@ l] ].
    intros.
    set (ga_comp Γ Δ ec l z a b) as q.

    set (@RLet Γ Δ) as q'.
    set (@RLet Γ Δ [@ga_mk _ ec z a @@ l] Σ (@ga_mk _ ec z b) (@ga_mk _ ec a b) l) as q''.
    eapply nd_comp.
    Focus 2.
    eapply nd_rule.
    eapply RArrange.
    apply RExch.

    eapply nd_comp.
    Focus 2.
    eapply nd_rule.
    apply q''.

    idtac.
    clear q'' q'.
    eapply nd_comp.
    apply nd_rlecnac.
    apply nd_prod.
    apply nd_id.
    apply q.
    Defined.

  Lemma ga_unkappa'     : ∀ Γ Δ ec l a b Σ x,
    ND Rule
    [Γ > Δ > Σ                          |- [@ga_mk Γ ec (a,,x)  b @@ l] ] 
    [Γ > Δ > Σ,,[@ga_mk Γ ec [] a @@ l] |- [@ga_mk Γ ec x       b @@ l] ].
    intros.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RLet ].
    eapply nd_comp; [ apply nd_llecnac | idtac ].
    apply nd_prod.
    apply ga_first.

    eapply nd_comp; [ idtac | eapply nd_rule; eapply RLet ].
    eapply nd_comp; [ apply nd_llecnac | idtac ].
    apply nd_prod.
    apply postcompose.
    apply ga_uncancell.
    apply precompose.
    Defined.

  Lemma ga_kappa'     : ∀ Γ Δ ec l a b Σ x,
    ND Rule
    [Γ > Δ > Σ,,[@ga_mk Γ ec [] a @@ l] |- [@ga_mk Γ ec x b @@ l] ]
    [Γ > Δ > Σ                          |- [@ga_mk Γ ec (a,,x)  b @@ l] ].
    apply (Prelude_error "ga_kappa not supported yet (BIG FIXME)").
    Defined.

  (* useful for cutting down on the pretty-printed noise
  
  Notation "`  x" := (take_lev _ x) (at level 20).
  Notation "`` x" := (mapOptionTree unlev x) (at level 20).
  Notation "``` x" := (drop_lev _ x) (at level 20).
  *)
  Definition flatten_arrangement' :
    forall Γ (Δ:CoercionEnv Γ)
      (ec:HaskTyVar Γ ECKind) (lev:HaskLevel Γ) (ant1 ant2:Tree ??(LeveledHaskType Γ ★)) (r:Arrange ant1 ant2),
      ND Rule [] [Γ > Δ > [] |- [@ga_mk _ (v2t ec) (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) ant2))
        (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) ant1)) @@ nil] ].

      intros Γ Δ ec lev.
      refine (fix flatten ant1 ant2 (r:Arrange ant1 ant2):
           ND Rule [] [Γ > Δ > [] |- [@ga_mk _ (v2t ec)
             (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) ant2))
             (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) ant1)) @@ nil]] :=
        match r as R in Arrange A B return
          ND Rule [] [Γ > Δ > [] |- [@ga_mk _ (v2t ec)
            (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) B))
            (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) A)) @@ nil]]
          with
          | RCanL  a             => let case_RCanL := tt  in ga_uncancell _ _ _ _ _
          | RCanR  a             => let case_RCanR := tt  in ga_uncancelr _ _ _ _ _
          | RuCanL a             => let case_RuCanL := tt in ga_cancell _ _ _ _ _
          | RuCanR a             => let case_RuCanR := tt in ga_cancelr _ _ _ _ _
          | RAssoc a b c         => let case_RAssoc := tt in ga_assoc _ _ _ _ _ _ _
          | RCossa a b c         => let case_RCossa := tt in ga_unassoc _ _ _ _ _ _ _
          | RExch  a b           => let case_RExch := tt  in ga_swap  _ _ _ _ _ _
          | RWeak  a             => let case_RWeak := tt  in ga_drop _ _ _ _ _ 
          | RCont  a             => let case_RCont := tt  in ga_copy  _ _ _ _ _ 
          | RLeft  a b c r'      => let case_RLeft := tt  in flatten _ _ r' ;; boost _ _ _ _ _ (ga_second _ _ _ _ _ _ _)
          | RRight a b c r'      => let case_RRight := tt in flatten _ _ r' ;; boost _ _ _ _ _ (ga_first  _ _ _ _ _ _ _)
          | RComp  c b a r1 r2   => let case_RComp := tt  in (fun r1' r2' => _) (flatten _ _ r1) (flatten _ _ r2)
        end); clear flatten; repeat take_simplify; repeat drop_simplify; intros.

        destruct case_RComp.
          set (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) a)) as a' in *.
          set (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) b)) as b' in *.
          set (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) c)) as c' in *.
          eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; apply RCanL ].
          eapply nd_comp; [ idtac | eapply nd_rule; apply
             (@RLet Γ Δ [] [] (@ga_mk _ (v2t ec) a' c') (@ga_mk _ (v2t ec) a' b')) ].
          eapply nd_comp; [ apply nd_llecnac | idtac ].
          apply nd_prod.
          apply r2'.
          eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; apply RuCanL ].
          eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; apply RCanR ].
          eapply nd_comp; [ idtac | eapply nd_rule;  apply 
            (@RLet Γ Δ [@ga_mk _ (v2t ec) a' b' @@ _] [] (@ga_mk _ (v2t ec) a' c') (@ga_mk _ (v2t ec) b' c'))].
          eapply nd_comp; [ apply nd_llecnac | idtac ].
          eapply nd_prod.
          apply r1'.
          apply ga_comp.
          Defined.

  Definition flatten_arrangement :
    forall Γ (Δ:CoercionEnv Γ) n
      (ec:HaskTyVar Γ ECKind) (lev:HaskLevel Γ) (ant1 ant2:Tree ??(LeveledHaskType Γ ★)) (r:Arrange ant1 ant2) succ,
      ND Rule
      [Γ > Δ > mapOptionTree (flatten_leveled_type ) (drop_lev n ant1)
        |- [@ga_mk _ (v2t ec)
          (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) ant1))
          (mapOptionTree (flatten_type ○ unlev) succ) @@ nil]]
      [Γ > Δ > mapOptionTree (flatten_leveled_type ) (drop_lev n ant2)
        |- [@ga_mk _ (v2t ec)
          (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) ant2))
          (mapOptionTree (flatten_type ○ unlev) succ) @@ nil]].
      intros.
      refine ( _ ;; (boost _ _ _ _ _ (postcompose _ _ _ _ _ _ _ (flatten_arrangement' Γ Δ ec lev ant1 ant2 r)))).
      apply nd_rule.
      apply RArrange.
      refine ((fix flatten ant1 ant2 (r:Arrange ant1 ant2) :=
        match r as R in Arrange A B return
          Arrange (mapOptionTree (flatten_leveled_type ) (drop_lev _ A))
          (mapOptionTree (flatten_leveled_type ) (drop_lev _ B)) with
          | RCanL  a             => let case_RCanL := tt  in RCanL _
          | RCanR  a             => let case_RCanR := tt  in RCanR _
          | RuCanL a             => let case_RuCanL := tt in RuCanL _
          | RuCanR a             => let case_RuCanR := tt in RuCanR _
          | RAssoc a b c         => let case_RAssoc := tt in RAssoc _ _ _
          | RCossa a b c         => let case_RCossa := tt in RCossa _ _ _
          | RExch  a b           => let case_RExch := tt  in RExch _ _
          | RWeak  a             => let case_RWeak := tt  in RWeak _
          | RCont  a             => let case_RCont := tt  in RCont _
          | RLeft  a b c r'      => let case_RLeft := tt  in RLeft  _ (flatten _ _ r')
          | RRight a b c r'      => let case_RRight := tt in RRight _ (flatten _ _ r')
          | RComp  a b c r1 r2   => let case_RComp := tt  in RComp    (flatten _ _ r1) (flatten _ _ r2)
        end) ant1 ant2 r); clear flatten; repeat take_simplify; repeat drop_simplify; intros.
        Defined.

  Definition flatten_arrangement'' :
    forall  Γ Δ ant1 ant2 succ (r:Arrange ant1 ant2),
      ND Rule (mapOptionTree (flatten_judgment ) [Γ > Δ > ant1 |- succ])
      (mapOptionTree (flatten_judgment ) [Γ > Δ > ant2 |- succ]).
    intros.
    simpl.
    set (getjlev succ) as succ_lev.
    assert (succ_lev=getjlev succ).
      reflexivity.

    destruct succ_lev.
      apply nd_rule.
      apply RArrange.
      induction r; simpl.
        apply RCanL.
        apply RCanR.
        apply RuCanL.
        apply RuCanR.
        apply RAssoc.
        apply RCossa.
        apply RExch.
        apply RWeak.
        apply RCont.
        apply RLeft; auto.
        apply RRight; auto.
        eapply RComp; [ apply IHr1 | apply IHr2 ].

      apply flatten_arrangement.
        apply r.
        Defined.

  Definition ga_join Γ Δ Σ₁ Σ₂ a b ec :
    ND Rule [] [Γ > Δ > Σ₁     |- [@ga_mk _ ec [] a      @@ nil]] ->
    ND Rule [] [Γ > Δ > Σ₂     |- [@ga_mk _ ec [] b      @@ nil]] ->
    ND Rule [] [Γ > Δ > Σ₁,,Σ₂ |- [@ga_mk _ ec [] (a,,b) @@ nil]].
    intro pfa.
    intro pfb.
    apply secondify with (c:=a)  in pfb.
    eapply nd_comp.
    Focus 2.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RLet ].
    eapply nd_comp; [ eapply nd_llecnac | idtac ].
    eapply nd_prod.
    apply pfb.
    clear pfb.
    apply postcompose'.
    eapply nd_comp.
    apply pfa.
    clear pfa.
    apply boost.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply RCanL ].
    apply precompose'.
    apply ga_uncancelr.
    apply nd_id.
    Defined.

  Definition arrange_brak : forall Γ Δ ec succ t,
   ND Rule
     [Γ > Δ > mapOptionTree (flatten_leveled_type ) (drop_lev (ec :: nil) succ),,
      [(@ga_mk _ (v2t ec) [] (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: nil) succ))) @@  nil] |- [t @@ nil]]
     [Γ > Δ > mapOptionTree (flatten_leveled_type ) succ |- [t @@  nil]].
    intros.
    unfold drop_lev.
    set (@arrange' _ succ (levelMatch (ec::nil))) as q.
    set (arrangeMap _ _ flatten_leveled_type q) as y.
    eapply nd_comp.
    Focus 2.
    eapply nd_rule.
    eapply RArrange.
    apply y.
    idtac.
    clear y q.
    simpl.
    eapply nd_comp; [ apply nd_llecnac | idtac ].
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RLet ].
    apply nd_prod.
    Focus 2.
    apply nd_id.
    idtac.
    induction succ; try destruct a; simpl.
    unfold take_lev.
    unfold mkTakeFlags.
    unfold mkFlags.
    unfold bnot.
    simpl.
    destruct l as [t' lev'].
    destruct lev' as [|ec' lev'].
    simpl.
    apply ga_id.
    unfold levelMatch.
    set (@eqd_dec (HaskLevel Γ) (haskLevelEqDecidable Γ) (ec' :: lev') (ec :: nil)) as q.
    destruct q.
    inversion e; subst.
    simpl.
    apply nd_rule.
    unfold flatten_leveled_type.
    simpl.
    unfold flatten_type.
    simpl.
    unfold ga_mk.
    simpl.
    apply RVar.
    simpl.
    apply ga_id.
    apply ga_id.
    unfold take_lev.
    simpl.
    apply ga_join.
      apply IHsucc1.
      apply IHsucc2.
    Defined.

  Definition arrange_esc : forall Γ Δ ec succ t,
   ND Rule
     [Γ > Δ > mapOptionTree (flatten_leveled_type ) succ |- [t @@  nil]]
     [Γ > Δ > mapOptionTree (flatten_leveled_type ) (drop_lev (ec :: nil) succ),,
      [(@ga_mk _ (v2t ec) [] (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: nil) succ))) @@  nil] |- [t @@  nil]].
    intros.
    unfold drop_lev.
    set (@arrange _ succ (levelMatch (ec::nil))) as q.
    set (arrangeMap _ _ flatten_leveled_type q) as y.
    eapply nd_comp.
    eapply nd_rule.
    eapply RArrange.
    apply y.
    idtac.
    clear y q.

    induction succ.
    destruct a.
      destruct l.
      simpl.
      unfold mkDropFlags; simpl.
      unfold take_lev.
      unfold mkTakeFlags.
      simpl.
      destruct (General.list_eq_dec h0 (ec :: nil)).
        simpl.
        rewrite e.
        apply nd_id.
        simpl.
        apply nd_rule.
        apply RArrange.
        apply RLeft.
        apply RWeak.
      simpl.
        apply nd_rule.
        unfold take_lev.
        simpl.
        apply RArrange.
        apply RLeft.
        apply RWeak.
      apply (Prelude_error "escapifying code with multi-leaf antecedents is not supported").
      Defined.

  Lemma mapOptionTree_distributes
    : forall T R (a b:Tree ??T) (f:T->R),
      mapOptionTree f (a,,b) = (mapOptionTree f a),,(mapOptionTree f b).
    reflexivity.
    Qed.

  Definition decide_tree_empty : forall {T:Type}(t:Tree ??T),
    sum { q:Tree unit & t = mapTree (fun _ => None) q } unit.
    intro T.
    refine (fix foo t :=
      match t with
        | T_Leaf x => _
        | T_Branch b1 b2 => let b1' := foo b1 in let b2' := foo b2 in _
      end).
    intros.
    destruct x.
    right; apply tt.
    left.
      exists (T_Leaf tt).
      auto.
    destruct b1'.
    destruct b2'.
    destruct s.
    destruct s0.
    subst.
    left.
    exists (x,,x0).
    reflexivity.
    right; auto.
    right; auto.
    Defined.

  Lemma unlev_relev : forall {Γ}(t:Tree ??(HaskType Γ ★)) lev, mapOptionTree unlev (t @@@ lev) = t.
    intros.
    induction t.
    destruct a; reflexivity.
    rewrite <- IHt1 at 2.
    rewrite <- IHt2 at 2.
    reflexivity.
    Qed.

  Lemma tree_of_nothing : forall Γ ec t a,
    Arrange (a,,mapOptionTree flatten_leveled_type (drop_lev(Γ:=Γ) (ec :: nil) (t @@@ (ec :: nil)))) a.
    intros.
    induction t; try destruct o; try destruct a0.
    simpl.
    drop_simplify.
    simpl.
    apply RCanR.
    simpl.
    apply RCanR.
    Opaque drop_lev.
    simpl.
    Transparent drop_lev.
    drop_simplify.
    simpl.
    eapply RComp.
    eapply RComp.
    eapply RAssoc.
    eapply RRight.
    apply IHt1.
    apply IHt2.
    Defined.

  Lemma tree_of_nothing' : forall Γ ec t a,
    Arrange a (a,,mapOptionTree flatten_leveled_type (drop_lev(Γ:=Γ) (ec :: nil) (t @@@ (ec :: nil)))).
    intros.
    induction t; try destruct o; try destruct a0.
    simpl.
    drop_simplify.
    simpl.
    apply RuCanR.
    simpl.
    apply RuCanR.
    Opaque drop_lev.
    simpl.
    Transparent drop_lev.
    drop_simplify.
    simpl.
    eapply RComp.
    Focus 2.
    eapply RComp.
    Focus 2.
    eapply RCossa.
    Focus 2.
    eapply RRight.
    apply IHt1.
    apply IHt2.
    Defined.

  Lemma krunk : forall Γ (ec:HaskTyVar Γ ECKind) t,
    flatten_type (<[ ec |- t ]>)
    = @ga_mk Γ (v2t ec)
    (mapOptionTree flatten_type (take_arg_types_as_tree t))
    [ flatten_type (drop_arg_types_as_tree   t)].

    intros.
    unfold flatten_type at 1.
    simpl.
    unfold ga_mk.
    unfold v2t.
    admit. (* BIG HUGE CHEAT FIXME *)
    Qed.

  Definition flatten_proof :
    forall  {h}{c},
      ND SRule h c ->
      ND  Rule (mapOptionTree (flatten_judgment ) h) (mapOptionTree (flatten_judgment ) c).
    intros.
    eapply nd_map'; [ idtac | apply X ].
    clear h c X.
    intros.
    simpl in *.

    refine 
      (match X as R in SRule H C with
      | SBrak    Γ Δ t ec succ lev           => let case_SBrak := tt         in _
      | SEsc     Γ Δ t ec succ lev           => let case_SEsc := tt          in _
      | SFlat    h c r                       => let case_SFlat := tt         in _
      end).

    destruct case_SFlat.
    refine (match r as R in Rule H C with
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
      apply (flatten_arrangement''  Γ Δ a b x d).

    destruct case_RBrak.
      apply (Prelude_error "found unskolemized Brak rule; this shouldn't happen").

    destruct case_REsc.
      apply (Prelude_error "found unskolemized Esc rule; this shouldn't happen").
      
    destruct case_RNote.
      simpl.
      destruct l; simpl.
        apply nd_rule; apply RNote; auto.
        apply nd_rule; apply RNote; auto.

    destruct case_RLit.
      simpl.
      destruct l0; simpl.
        unfold flatten_leveled_type.
        simpl.
        rewrite literal_types_unchanged.
          apply nd_rule; apply RLit.
        unfold take_lev; simpl.
        unfold drop_lev; simpl.
        simpl.
        rewrite literal_types_unchanged.
        apply ga_lit.

    destruct case_RVar.
      Opaque flatten_judgment.
      simpl.
      Transparent flatten_judgment.
      idtac.
      unfold flatten_judgment.
      unfold getjlev.
      destruct lev.
      apply nd_rule. apply RVar.
      repeat drop_simplify.      
      repeat take_simplify.
      simpl.
      apply ga_id.      

    destruct case_RGlobal.
      simpl.
      rename l into g.
      rename σ into l.
      destruct l as [|ec lev]; simpl. 
        destruct (eqd_dec (g:CoreVar) (hetmet_flatten:CoreVar)).
          set (flatten_type (g wev)) as t.
          set (RGlobal _ Δ nil (mkGlobal Γ t hetmet_id)) as q.
          simpl in q.
          apply nd_rule.
          apply q.
          apply INil.
        destruct (eqd_dec (g:CoreVar) (hetmet_unflatten:CoreVar)).
          set (flatten_type (g wev)) as t.
          set (RGlobal _ Δ nil (mkGlobal Γ t hetmet_id)) as q.
          simpl in q.
          apply nd_rule.
          apply q.
          apply INil.
        unfold flatten_leveled_type. simpl.
          apply nd_rule; rewrite globals_do_not_have_code_types.
          apply RGlobal.
      apply (Prelude_error "found RGlobal at depth >0; globals should never appear inside code brackets unless escaped").

    destruct case_RLam.
      Opaque drop_lev.
      Opaque take_lev.
      simpl.
      destruct lev as [|ec lev]; simpl; [ apply nd_rule; apply RLam; auto | idtac ].
      repeat drop_simplify.
      repeat take_simplify.
      eapply nd_comp.
        eapply nd_rule.
        eapply RArrange.
        simpl.
        apply RCanR.
      apply boost.
      simpl.
      apply ga_curry.

    destruct case_RCast.
      simpl.
      destruct lev as [|ec lev]; simpl; [ apply nd_rule; apply RCast; auto | idtac ].
      simpl.
      apply flatten_coercion; auto.
      apply (Prelude_error "RCast at level >0; casting inside of code brackets is currently not supported").

    destruct case_RJoin.
      simpl.
      destruct (getjlev x); destruct (getjlev q);
        [ apply nd_rule; apply RJoin | idtac | idtac | idtac ];
        apply (Prelude_error "RJoin at depth >0").

    destruct case_RApp.
      simpl.

      destruct lev as [|ec lev]. simpl. apply nd_rule.
        unfold flatten_leveled_type at 4.
        unfold flatten_leveled_type at 2.
        simpl.
        replace (flatten_type (tx ---> te))
          with (flatten_type tx ---> flatten_type te).
        apply RApp.
        reflexivity.

        repeat drop_simplify.
          repeat take_simplify.
          rewrite mapOptionTree_distributes.
          set (mapOptionTree (flatten_leveled_type ) (drop_lev (ec :: lev) Σ₁)) as Σ₁'.
          set (mapOptionTree (flatten_leveled_type ) (drop_lev (ec :: lev) Σ₂)) as Σ₂'.
          set (take_lev (ec :: lev) Σ₁) as Σ₁''.
          set (take_lev (ec :: lev) Σ₂) as Σ₂''.
          replace (flatten_type  (tx ---> te)) with ((flatten_type  tx) ---> (flatten_type  te)).
          apply (Prelude_error "FIXME: ga_apply").
          reflexivity.

(*
  Notation "`  x" := (take_lev _ x).
  Notation "`` x" := (mapOptionTree unlev x) (at level 20).
  Notation "``` x" := ((drop_lev _ x)) (at level 20).
  Notation "!<[]> x" := (flatten_type _ x) (at level 1).
  Notation "!<[@]> x" := (mapOptionTree flatten_leveled_type x) (at level 1).
*)

    destruct case_RLet.
      simpl.
      destruct lev as [|ec lev]; simpl; [ apply nd_rule; apply RLet; auto | idtac ].
      repeat drop_simplify.
      repeat take_simplify.
      simpl.

      eapply nd_comp.
      eapply nd_prod; [ idtac | apply nd_id ].
      eapply boost.
      apply ga_second.

      eapply nd_comp.
      eapply nd_prod.
      apply nd_id.
      eapply nd_comp.
      eapply nd_rule.
      eapply RArrange.
      apply RCanR.
      eapply precompose.

      apply nd_rule.
      apply RLet.

    destruct case_RVoid.
      simpl.
      apply nd_rule.
      apply RVoid.
        
    destruct case_RAppT.
      simpl. destruct lev; simpl.
      unfold flatten_leveled_type.
      simpl.
      rewrite flatten_commutes_with_HaskTAll.
      rewrite flatten_commutes_with_substT.
      apply nd_rule.
      apply RAppT.
      apply Δ.
      apply Δ.
      apply (Prelude_error "found type application at level >0; this is not supported").

    destruct case_RAbsT.
      simpl. destruct lev; simpl.
      unfold flatten_leveled_type at 4.
      unfold flatten_leveled_type at 2.
      simpl.
      rewrite flatten_commutes_with_HaskTAll.
      rewrite flatten_commutes_with_HaskTApp.
      eapply nd_comp; [ idtac | eapply nd_rule; eapply RAbsT ].
      simpl.
      set (mapOptionTree (flatten_leveled_type ) (mapOptionTree (weakLT(κ:=κ)) Σ)) as a.
      set (mapOptionTree (weakLT(κ:=κ)) (mapOptionTree (flatten_leveled_type ) Σ)) as q'.
      assert (a=q').
        unfold a.
        unfold q'.
        clear a q'.
        induction Σ.
          destruct a.
          simpl.
          rewrite flatten_commutes_with_weakLT.
          reflexivity.
          reflexivity.
          simpl.
          rewrite <- IHΣ1.
          rewrite <- IHΣ2.
          reflexivity.
      rewrite H.
      apply nd_id.
      apply Δ.
      apply Δ.
      apply (Prelude_error "found type abstraction at level >0; this is not supported").

    destruct case_RAppCo.
      simpl. destruct lev; simpl.
      unfold flatten_leveled_type at 4.
      unfold flatten_leveled_type at 2.
      unfold flatten_type.
      simpl.
      apply nd_rule.
      apply RAppCo.
      apply flatten_coercion.
      apply γ.
      apply (Prelude_error "found coercion application at level >0; this is not supported").

    destruct case_RAbsCo.
      simpl. destruct lev; simpl.
      unfold flatten_type.
      simpl.
      apply (Prelude_error "AbsCo not supported (FIXME)").
      apply (Prelude_error "found coercion abstraction at level >0; this is not supported").

    destruct case_RLetRec.
      rename t into lev.
      simpl.
      apply (Prelude_error "LetRec not supported (FIXME)").

    destruct case_RCase.
      simpl.
      apply (Prelude_error "Case not supported (BIG FIXME)").

    destruct case_SBrak.
      simpl.
      destruct lev.
      drop_simplify.
      set (drop_lev (ec :: nil) (take_arg_types_as_tree t @@@ (ec :: nil))) as empty_tree.
      take_simplify.
      rewrite take_lemma'.
      simpl.
      rewrite mapOptionTree_compose.
      rewrite mapOptionTree_compose.
      rewrite unlev_relev.
      rewrite <- mapOptionTree_compose.
      unfold flatten_leveled_type at 4.
      simpl.
      rewrite krunk.
      set (mapOptionTree flatten_leveled_type (drop_lev (ec :: nil) succ)) as succ_host.
      set (mapOptionTree (flatten_type ○ unlev)(take_lev (ec :: nil) succ)) as succ_guest.
      set (mapOptionTree flatten_type (take_arg_types_as_tree t)) as succ_args.
      unfold empty_tree.
      eapply nd_comp; [ eapply nd_rule; eapply RArrange; apply tree_of_nothing | idtac ].
      refine (ga_unkappa' Γ Δ (v2t ec) nil _ _ _ _ ;; _).
      unfold succ_host.
      unfold succ_guest.
      apply arrange_brak.
      apply (Prelude_error "found Brak at depth >0 indicating 3-level code; only two-level code is currently supported").

    destruct case_SEsc.
      simpl.
      destruct lev.
      simpl.
      unfold flatten_leveled_type at 2.
      simpl.
      rewrite krunk.
      rewrite mapOptionTree_compose.
      take_simplify.
      drop_simplify.
      simpl.
      eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; apply tree_of_nothing' ].
      simpl.
      rewrite take_lemma'.
      rewrite unlev_relev.
      rewrite <- mapOptionTree_compose.
      eapply nd_comp; [ apply (arrange_esc _ _ ec) | idtac ].

      set (decide_tree_empty (take_lev (ec :: nil) succ)) as q'.
      destruct q'.
      destruct s.
      rewrite e.
      clear e.

      set (mapOptionTree flatten_leveled_type (drop_lev (ec :: nil) succ)) as succ_host.
      set (mapOptionTree flatten_type (take_arg_types_as_tree t)) as succ_args.

      eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; apply RCanR ].
      eapply nd_comp; [ idtac | eapply nd_rule; eapply RLet ].
      eapply nd_comp; [ apply nd_llecnac | idtac ].
      apply nd_prod; [ idtac | eapply boost ].
      induction x.
        apply ga_id.
        eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply RCanR ].
        simpl.
        apply ga_join.
          apply IHx1.
          apply IHx2.
          simpl.
          apply postcompose.

      refine ( _ ;; (boost _ _ _ _ _ (postcompose _ _ _ _ _ _ _ _))).
      apply ga_cancell.
      apply firstify.

      induction x.
        destruct a; simpl.
        apply ga_id.
        simpl.
        refine ( _ ;; (boost _ _ _ _ _ (postcompose _ _ _ _ _ _ _ _))).
        apply ga_cancell.
        refine ( _ ;; (boost _ _ _ _ _ (postcompose _ _ _ _ _ _ _ _))).
        eapply firstify.
        apply IHx1.
        apply secondify.
        apply IHx2.

      (* environment has non-empty leaves *)
      apply ga_kappa'.

      (* nesting too deep *)
      apply (Prelude_error "found Esc at depth >0 indicating 3-level code; only two-level code is currently supported").
      Defined.

  Definition skolemize_and_flatten_proof :
    forall  {h}{c},
      ND  Rule h c ->
      ND  Rule
           (mapOptionTree (flatten_judgment ○ skolemize_judgment) h)
           (mapOptionTree (flatten_judgment ○ skolemize_judgment) c).
    intros.
    rewrite mapOptionTree_compose.
    rewrite mapOptionTree_compose.
    apply flatten_proof.
    apply skolemize_proof.
    apply X.
    Defined.


  (* to do: establish some metric on judgments (max length of level of any succedent type, probably), show how to
   * calculate it, and show that the flattening procedure above drives it down by one *)

  (*
  Instance FlatteningFunctor {Γ}{Δ}{ec} : Functor (JudgmentsL (PCF Γ Δ ec)) (TypesL (SystemFCa Γ Δ)) (obact) :=
    { fmor := FlatteningFunctor_fmor }.

  Definition ReificationFunctor Γ Δ : Functor (JudgmentsL _ _ (PCF n Γ Δ)) SystemFCa' (mapOptionTree brakifyJudg).
    refine {| fmor := ReificationFunctor_fmor Γ Δ |}; unfold hom; unfold ob; simpl ; intros.

  Definition PCF_SMME (n:nat)(Γ:TypeEnv)(Δ:CoercionEnv Γ) : ProgrammingLanguageSMME.
    refine {| plsmme_pl := PCF n Γ Δ |}.
    Defined.

  Definition SystemFCa_SMME (n:nat)(Γ:TypeEnv)(Δ:CoercionEnv Γ) : ProgrammingLanguageSMME.
    refine {| plsmme_pl := SystemFCa n Γ Δ |}.
    Defined.

  Definition ReificationFunctorMonoidal n : MonoidalFunctor (JudgmentsN n) (JudgmentsN (S n)) (ReificationFunctor n).
    Defined.

  (* 5.1.4 *)
  Definition PCF_SystemFCa_two_level n Γ Δ : TwoLevelLanguage (PCF_SMME n Γ Δ) (SystemFCa_SMME (S n) Γ Δ).
    Defined.
  *)
  (*  ... and the retraction exists *)

End HaskFlattener.

Implicit Arguments garrow [ ].
