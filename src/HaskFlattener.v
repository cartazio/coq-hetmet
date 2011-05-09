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

  Context (hetmet_flatten : WeakExprVar).
  Context (hetmet_unflatten : WeakExprVar).
  Context (hetmet_id      : WeakExprVar).
  Context {unitTy : forall TV, RawHaskType TV ★                                          }.
  Context {prodTy : forall TV, RawHaskType TV ★  -> RawHaskType TV ★ -> RawHaskType TV ★ }.
  Context {gaTy   : forall TV, RawHaskType TV ECKind  -> RawHaskType TV ★ -> RawHaskType TV ★  -> RawHaskType TV ★ }.

  Definition ga_mk_tree {Γ} (tr:Tree ??(HaskType Γ ★)) : HaskType Γ ★ :=
    fun TV ite => reduceTree (unitTy TV) (prodTy TV) (mapOptionTree (fun x => x TV ite) tr).

  Definition ga_mk {Γ}(ec:HaskType Γ ECKind )(ant suc:Tree ??(HaskType Γ ★)) : HaskType Γ ★ :=
    fun TV ite => gaTy TV (ec TV ite) (ga_mk_tree ant TV ite) (ga_mk_tree suc TV ite).

  Class garrow :=
  { ga_id        : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                           [] |- [@ga_mk Γ ec a a @@ l] ]
  ; ga_cancelr   : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                           [] |- [@ga_mk Γ ec (a,,[]) a @@ l] ]
  ; ga_cancell   : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                           [] |- [@ga_mk Γ ec ([],,a) a @@ l] ]
  ; ga_uncancelr : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                           [] |- [@ga_mk Γ ec a (a,,[]) @@ l] ]
  ; ga_uncancell : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                           [] |- [@ga_mk Γ ec a ([],,a) @@ l] ]
  ; ga_assoc     : ∀ Γ Δ ec l a b c, ND Rule [] [Γ > Δ >                           [] |- [@ga_mk Γ ec ((a,,b),,c) (a,,(b,,c)) @@ l] ]
  ; ga_unassoc   : ∀ Γ Δ ec l a b c, ND Rule [] [Γ > Δ >                           [] |- [@ga_mk Γ ec (a,,(b,,c)) ((a,,b),,c) @@ l] ]
  ; ga_swap      : ∀ Γ Δ ec l a b  , ND Rule [] [Γ > Δ >                           [] |- [@ga_mk Γ ec (a,,b) (b,,a) @@ l] ]
  ; ga_drop      : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                           [] |- [@ga_mk Γ ec a [] @@ l] ]
  ; ga_copy      : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                           [] |- [@ga_mk Γ ec a (a,,a) @@ l] ]
  ; ga_first     : ∀ Γ Δ ec l a b x, ND Rule [] [Γ > Δ >          [@ga_mk Γ ec a b @@ l] |- [@ga_mk Γ ec (a,,x) (b,,x) @@ l] ]
  ; ga_second    : ∀ Γ Δ ec l a b x, ND Rule [] [Γ > Δ >          [@ga_mk Γ ec a b @@ l] |- [@ga_mk Γ ec (x,,a) (x,,b) @@ l] ]
  ; ga_lit       : ∀ Γ Δ ec l lit  , ND Rule [] [Γ > Δ >                           [] |- [@ga_mk Γ ec [] [literalType lit] @@ l] ]
  ; ga_curry     : ∀ Γ Δ ec l a b c, ND Rule [] [Γ > Δ > [@ga_mk Γ ec (a,,[b]) [c] @@ l] |- [@ga_mk Γ ec a [b ---> c] @@ l] ]
  ; ga_comp      : ∀ Γ Δ ec l a b c, ND Rule [] [Γ > Δ > [@ga_mk Γ ec a b @@ l],,[@ga_mk Γ ec b c @@ l] |- [@ga_mk Γ ec a c @@ l] ] 
  ; ga_apply     : ∀ Γ Δ ec l a a' b c, ND Rule []
                                  [Γ > Δ > [@ga_mk Γ ec a [b ---> c] @@ l],,[@ga_mk Γ ec a' [b] @@ l] |- [@ga_mk Γ ec (a,,a') [c] @@ l] ]
  ; ga_kappa     : ∀ Γ Δ ec l a b Σ, ND Rule
  [Γ > Δ > Σ,,[@ga_mk Γ ec [] a @@ l] |- [@ga_mk Γ ec [] b @@ l] ]
  [Γ > Δ > Σ          |- [@ga_mk Γ ec a  b @@ l] ]
  }.
  Context `(gar:garrow).

  Notation "a ~~~~> b" := (@ga_mk _ _ a b) (at level 20).

  (*
   *  The story:
   *    - code types <[t]>@c                                                become garrows  c () t 
   *    - free variables of type t at a level lev deeper than the succedent become garrows  c () t
   *    - free variables at the level of the succedent become 
   *)
  Fixpoint garrowfy_raw_codetypes {TV}{κ}(exp: RawHaskType TV κ) : RawHaskType TV κ :=
    match exp with
    | TVar    _  x          => TVar x
    | TAll     _ y          => TAll   _  (fun v => garrowfy_raw_codetypes (y v))
    | TApp   _ _ x y        => TApp      (garrowfy_raw_codetypes x) (garrowfy_raw_codetypes y)
    | TCon       tc         => TCon      tc
    | TCoerc _ t1 t2 t      => TCoerc    (garrowfy_raw_codetypes t1) (garrowfy_raw_codetypes t2)
                                         (garrowfy_raw_codetypes t)
    | TArrow                => TArrow
    | TCode      v e        => gaTy TV v (unitTy TV) (garrowfy_raw_codetypes e)
    | TyFunApp  tfc kl k lt => TyFunApp tfc kl k (garrowfy_raw_codetypes_list _ lt)
    end
    with garrowfy_raw_codetypes_list {TV}(lk:list Kind)(exp:@RawHaskTypeList TV lk) : @RawHaskTypeList TV lk :=
    match exp in @RawHaskTypeList _ LK return @RawHaskTypeList TV LK with
    | TyFunApp_nil               => TyFunApp_nil
    | TyFunApp_cons  κ kl t rest => TyFunApp_cons _ _ (garrowfy_raw_codetypes t) (garrowfy_raw_codetypes_list _ rest)
    end.
  Definition garrowfy_code_types {Γ}{κ}(ht:HaskType Γ κ) : HaskType Γ κ :=
    fun TV ite =>
      garrowfy_raw_codetypes (ht TV ite).

  Definition v2t {Γ}(ec:HaskTyVar Γ ECKind) := fun TV ite => TVar (ec TV ite).

  Fixpoint garrowfy_leveled_code_types' {Γ}(ht:HaskType Γ ★)(lev:HaskLevel Γ) : HaskType Γ ★ :=
    match lev with
      | nil      => garrowfy_code_types ht
      | ec::lev' => @ga_mk _ (v2t ec) [] [garrowfy_leveled_code_types' ht lev']
    end.

  Definition garrowfy_leveled_code_types {Γ}(ht:LeveledHaskType Γ ★) : LeveledHaskType Γ ★ :=
    match ht with
      htt @@ lev =>
      garrowfy_leveled_code_types' htt lev @@ nil
    end.

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

  Definition take_lev {Γ}(lev:HaskLevel Γ)(tt:Tree ??(LeveledHaskType Γ ★)) : Tree ??(HaskType Γ ★) :=
    mapOptionTree (fun x => garrowfy_code_types (unlev x)) (dropT (mkTakeFlags lev tt)).
(*
    mapOptionTree (fun x => garrowfy_code_types (unlev x))
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

  Lemma take_lemma : forall Γ (lev:HaskLevel Γ) x, take_lev lev [x @@  lev] = [garrowfy_code_types x].
    intros; simpl.
    Opaque eqd_dec.
    unfold take_lev.
    unfold mkTakeFlags.
    simpl.
    Transparent eqd_dec.
    eqd_dec_refl'.
    auto.
    Qed.

  Ltac drop_simplify :=
    match goal with
      | [ |- context[@drop_lev ?G ?L [ ?X @@ ?L ] ] ] =>
        rewrite (drop_lev_lemma G L X)
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
      | [ |- context[@take_lev ?G ?N (?A,,?B)] ] =>
      change (@take_lev G N (A,,B)) with ((@take_lev G N A),,(@take_lev G N B))
      | [ |- context[@take_lev ?G ?N (T_Leaf None)] ] =>
      change (@take_lev G N (T_Leaf (@None (LeveledHaskType G ★)))) with (T_Leaf (@None (LeveledHaskType G ★)))
    end.

  (* AXIOMS *)

  Axiom literal_types_unchanged : forall Γ l, garrowfy_code_types (literalType l) = literalType(Γ:=Γ) l.

  Axiom flatten_coercion : forall Γ Δ κ (σ τ:HaskType Γ κ) (γ:HaskCoercion Γ Δ (σ ∼∼∼ τ)),
    HaskCoercion Γ Δ (garrowfy_code_types σ ∼∼∼ garrowfy_code_types τ).

  Axiom garrowfy_commutes_with_substT :
    forall  κ Γ (Δ:CoercionEnv Γ) (σ:∀ TV, InstantiatedTypeEnv TV Γ → TV κ → RawHaskType TV ★) (τ:HaskType Γ κ),
    garrowfy_code_types  (substT σ τ) = substT (fun TV ite v => garrowfy_raw_codetypes  (σ TV ite v))
      (garrowfy_code_types  τ).

  Axiom garrowfy_commutes_with_HaskTAll :
    forall  κ Γ (Δ:CoercionEnv Γ) (σ:∀ TV, InstantiatedTypeEnv TV Γ → TV κ → RawHaskType TV ★),
    garrowfy_code_types  (HaskTAll κ σ) = HaskTAll κ (fun TV ite v => garrowfy_raw_codetypes (σ TV ite v)).

  Axiom garrowfy_commutes_with_HaskTApp :
    forall  κ Γ (Δ:CoercionEnv Γ) (σ:∀ TV, InstantiatedTypeEnv TV Γ → TV κ → RawHaskType TV ★),
    garrowfy_code_types  (HaskTApp (weakF σ) (FreshHaskTyVar κ)) =
    HaskTApp (weakF (fun TV ite v => garrowfy_raw_codetypes  (σ TV ite v))) (FreshHaskTyVar κ).

  Axiom garrowfy_commutes_with_weakLT : forall (Γ:TypeEnv) κ  t,
    garrowfy_leveled_code_types  (weakLT(Γ:=Γ)(κ:=κ) t) = weakLT(Γ:=Γ)(κ:=κ) (garrowfy_leveled_code_types  t).

  Axiom globals_do_not_have_code_types : forall (Γ:TypeEnv) (g:Global Γ) v,
    garrowfy_code_types (g v) = g v.

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

  Definition unlev' {Γ} (x:LeveledHaskType Γ ★) :=
    garrowfy_code_types (unlev x).

  (* "n" is the maximum depth remaining AFTER flattening *)
  Definition flatten_judgment (j:Judg) :=
    match j as J return Judg with
      Γ > Δ > ant |- suc =>
        match getjlev suc with
          | nil        => Γ > Δ > mapOptionTree garrowfy_leveled_code_types ant
                               |- mapOptionTree garrowfy_leveled_code_types suc

          | (ec::lev') => Γ > Δ > mapOptionTree garrowfy_leveled_code_types (drop_lev (ec::lev') ant)
                               |- [ga_mk (v2t ec)
                                         (take_lev (ec::lev') ant)
                                         (mapOptionTree unlev' suc)  (* we know the level of all of suc *)
                                         @@ nil]
        end
    end.

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
     eapply nd_comp; [ idtac | eapply nd_rule; apply (@RLet Γ Δ [@ga_mk _ ec b c @@lev] Σ (@ga_mk _ ec a c) (@ga_mk _ ec a b) lev) ].
     eapply nd_comp; [ apply nd_llecnac | idtac ].
     apply nd_prod.
     apply X.
     eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; apply RExch ].
     apply ga_comp.
     Defined.

  Definition precompose' : ∀ Γ Δ ec lev a b c Σ,
     ND Rule [] [ Γ > Δ > Σ                        |- [@ga_mk Γ ec b c @@ lev] ] ->
     ND Rule [] [ Γ > Δ > Σ,,[@ga_mk Γ ec a b @@ lev] |- [@ga_mk Γ ec a c @@ lev] ].
     intros.
     eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply RExch ].
     eapply nd_comp; [ idtac | eapply nd_rule; apply (@RLet Γ Δ [@ga_mk _ ec a b @@lev] Σ (@ga_mk _ ec a c) (@ga_mk _ ec b c) lev) ].
     eapply nd_comp; [ apply nd_llecnac | idtac ].
     apply nd_prod.
     apply X.
     apply ga_comp.
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

  Lemma ga_unkappa     : ∀ Γ Δ ec l a b Σ,
    ND Rule
    [Γ > Δ > Σ |- [@ga_mk Γ ec a  b @@ l] ] 
    [Γ > Δ > Σ,,[@ga_mk Γ ec [] a @@ l] |- [@ga_mk Γ ec [] b @@ l] ].
    intros.
    set (ga_comp Γ Δ ec l [] a b) as q.

    set (@RLet Γ Δ) as q'.
    set (@RLet Γ Δ [@ga_mk _ ec [] a @@ l] Σ (@ga_mk _ ec [] b) (@ga_mk _ ec a b) l) as q''.
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

  (* useful for cutting down on the pretty-printed noise
  
  Notation "`  x" := (take_lev _ x) (at level 20).
  Notation "`` x" := (mapOptionTree unlev x) (at level 20).
  Notation "``` x" := (drop_lev _ x) (at level 20).
  *)
  Definition garrowfy_arrangement' :
    forall Γ (Δ:CoercionEnv Γ)
      (ec:HaskTyVar Γ ECKind) (lev:HaskLevel Γ) (ant1 ant2:Tree ??(LeveledHaskType Γ ★)) (r:Arrange ant1 ant2),
      ND Rule [] [Γ > Δ > [] |- [@ga_mk _ (v2t ec) (take_lev (ec :: lev) ant2) (take_lev (ec :: lev) ant1) @@ nil] ].

      intros Γ Δ ec lev.
      refine (fix garrowfy ant1 ant2 (r:Arrange ant1 ant2):
           ND Rule [] [Γ > Δ > [] |- [@ga_mk _ (v2t ec) (take_lev (ec :: lev) ant2) (take_lev (ec :: lev) ant1) @@ nil]] :=
        match r as R in Arrange A B return
          ND Rule [] [Γ > Δ > [] |- [@ga_mk _ (v2t ec) (take_lev (ec :: lev) B) (take_lev (ec :: lev) A) @@ nil]]
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
          | RLeft  a b c r'      => let case_RLeft := tt  in garrowfy _ _ r' ;; boost _ _ _ _ _ (ga_second _ _ _ _ _ _ _)
          | RRight a b c r'      => let case_RRight := tt in garrowfy _ _ r' ;; boost _ _ _ _ _ (ga_first  _ _ _ _ _ _ _)
          | RComp  c b a r1 r2   => let case_RComp := tt  in (fun r1' r2' => _) (garrowfy _ _ r1) (garrowfy _ _ r2)
        end); clear garrowfy; repeat take_simplify; repeat drop_simplify; intros.

        destruct case_RComp.
          set (take_lev (ec :: lev) a) as a' in *.
          set (take_lev (ec :: lev) b) as b' in *.
          set (take_lev (ec :: lev) c) as c' in *.
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

  Definition garrowfy_arrangement :
    forall Γ (Δ:CoercionEnv Γ) n
      (ec:HaskTyVar Γ ECKind) (lev:HaskLevel Γ) (ant1 ant2:Tree ??(LeveledHaskType Γ ★)) (r:Arrange ant1 ant2) succ,
      ND Rule
      [Γ > Δ > mapOptionTree (garrowfy_leveled_code_types ) (drop_lev n ant1)
        |- [@ga_mk _ (v2t ec) (take_lev (ec :: lev) ant1) (mapOptionTree (unlev' ) succ) @@ nil]]
      [Γ > Δ > mapOptionTree (garrowfy_leveled_code_types ) (drop_lev n ant2)
        |- [@ga_mk _ (v2t ec) (take_lev (ec :: lev) ant2) (mapOptionTree (unlev' ) succ) @@ nil]].
      intros.
      refine ( _ ;; (boost _ _ _ _ _ (postcompose _ _ _ _ _ _ _ (garrowfy_arrangement' Γ Δ ec lev ant1 ant2 r)))).
      apply nd_rule.
      apply RArrange.
      refine ((fix garrowfy ant1 ant2 (r:Arrange ant1 ant2) :=
        match r as R in Arrange A B return
          Arrange (mapOptionTree (garrowfy_leveled_code_types ) (drop_lev _ A))
          (mapOptionTree (garrowfy_leveled_code_types ) (drop_lev _ B)) with
          | RCanL  a             => let case_RCanL := tt  in RCanL _
          | RCanR  a             => let case_RCanR := tt  in RCanR _
          | RuCanL a             => let case_RuCanL := tt in RuCanL _
          | RuCanR a             => let case_RuCanR := tt in RuCanR _
          | RAssoc a b c         => let case_RAssoc := tt in RAssoc _ _ _
          | RCossa a b c         => let case_RCossa := tt in RCossa _ _ _
          | RExch  a b           => let case_RExch := tt  in RExch _ _
          | RWeak  a             => let case_RWeak := tt  in RWeak _
          | RCont  a             => let case_RCont := tt  in RCont _
          | RLeft  a b c r'      => let case_RLeft := tt  in RLeft  _ (garrowfy _ _ r')
          | RRight a b c r'      => let case_RRight := tt in RRight _ (garrowfy _ _ r')
          | RComp  a b c r1 r2   => let case_RComp := tt  in RComp    (garrowfy _ _ r1) (garrowfy _ _ r2)
        end) ant1 ant2 r); clear garrowfy; repeat take_simplify; repeat drop_simplify; intros.
        Defined.

  Definition flatten_arrangement :
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

      apply garrowfy_arrangement.
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
     [Γ > Δ > mapOptionTree (garrowfy_leveled_code_types ) (drop_lev (ec :: nil) succ),,
      [(@ga_mk _ (v2t ec) [] (take_lev (ec :: nil) succ)) @@  nil] |- [(@ga_mk _ (v2t ec) [] [garrowfy_code_types  t]) @@  nil]]
     [Γ > Δ > mapOptionTree (garrowfy_leveled_code_types ) succ |- [(@ga_mk _ (v2t ec) [] [garrowfy_code_types  t]) @@  nil]].
    intros.
    unfold drop_lev.
    set (@arrange' _ succ (levelMatch (ec::nil))) as q.
    set (arrangeMap _ _ garrowfy_leveled_code_types q) as y.
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
     [Γ > Δ > mapOptionTree (garrowfy_leveled_code_types ) succ |- [(@ga_mk _ (v2t ec) [] [garrowfy_code_types  t]) @@  nil]]
     [Γ > Δ > mapOptionTree (garrowfy_leveled_code_types ) (drop_lev (ec :: nil) succ),,
      [(@ga_mk _ (v2t ec) [] (take_lev (ec :: nil) succ)) @@  nil] |- [(@ga_mk _ (v2t ec) [] [garrowfy_code_types  t]) @@  nil]].
    intros.
    unfold drop_lev.
    set (@arrange _ succ (levelMatch (ec::nil))) as q.
    set (arrangeMap _ _ garrowfy_leveled_code_types q) as y.
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
        unfold garrowfy_leveled_code_types'.
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

   
  Definition flatten_proof :
    forall  {h}{c},
      ND Rule h c ->
      ND Rule (mapOptionTree (flatten_judgment ) h) (mapOptionTree (flatten_judgment ) c).
    intros.
    eapply nd_map'; [ idtac | apply X ].
    clear h c X.
    intros.
    simpl in *.

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
      apply (flatten_arrangement  Γ Δ a b x d).

    destruct case_RBrak.
      simpl.
      destruct lev.
      change ([garrowfy_code_types  (<[ ec |- t ]>) @@  nil])
        with ([ga_mk (v2t ec) [] [garrowfy_code_types  t] @@  nil]).
      refine (ga_unkappa Γ Δ (v2t ec) nil (take_lev (ec::nil) succ) _
        (mapOptionTree (garrowfy_leveled_code_types) (drop_lev (ec::nil) succ)) ;; _ ).
      apply arrange_brak.
      apply (Prelude_error "found Brak at depth >0 (a)").

    destruct case_REsc.
      simpl.
      destruct lev.
      simpl.
      change ([garrowfy_code_types (<[ ec |- t ]>) @@  nil])
        with ([ga_mk (v2t ec) [] [garrowfy_code_types  t] @@  nil]).
      eapply nd_comp; [ apply arrange_esc | idtac ].
      set (decide_tree_empty (take_lev (ec :: nil) succ)) as q'.
      destruct q'.
      destruct s.
      rewrite e.
      clear e.

      eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply RCanR ].
      eapply nd_comp; [ idtac | eapply nd_rule; eapply RLet ].
      eapply nd_comp; [ apply nd_llecnac | idtac ].
      apply nd_prod; [ idtac | eapply boost ].
      induction x.
      apply ga_id.
      eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply RCanR ].
      apply ga_join.
      apply IHx1.
      apply IHx2.
      unfold unlev'.
      simpl.
      apply postcompose.
      apply ga_drop.

      (* environment has non-empty leaves *)
      apply (ga_kappa Γ Δ (v2t ec) nil (take_lev (ec::nil) succ) _ _).
      apply (Prelude_error "found Esc at depth >0 (a)").
      
    destruct case_RNote.
      simpl.
      destruct l; simpl.
        apply nd_rule; apply RNote; auto.
        apply nd_rule; apply RNote; auto.

    destruct case_RLit.
      simpl.
      destruct l0; simpl.
        rewrite literal_types_unchanged.
          apply nd_rule; apply RLit.
        unfold take_lev; simpl.
        unfold drop_lev; simpl.
        unfold unlev'.
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
      unfold unlev'.
      repeat take_simplify.
      simpl.
      apply ga_id.      

    destruct case_RGlobal.
      simpl.
      rename l into g.
      rename σ into l.
      destruct l as [|ec lev]; simpl. 
        destruct (eqd_dec (g:CoreVar) (hetmet_flatten:CoreVar)).
          set (garrowfy_code_types (g wev)) as t.
          set (RGlobal _ Δ nil (mkGlobal Γ t hetmet_id)) as q.
          simpl in q.
          apply nd_rule.
          apply q.
          apply INil.
        destruct (eqd_dec (g:CoreVar) (hetmet_unflatten:CoreVar)).
          set (garrowfy_code_types (g wev)) as t.
          set (RGlobal _ Δ nil (mkGlobal Γ t hetmet_id)) as q.
          simpl in q.
          apply nd_rule.
          apply q.
          apply INil.
        apply nd_rule; rewrite globals_do_not_have_code_types.
          apply RGlobal.
      apply (Prelude_error "found RGlobal at depth >0").

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
      apply ga_curry.

    destruct case_RCast.
      simpl.
      destruct lev as [|ec lev]; simpl; [ apply nd_rule; apply RCast; auto | idtac ].
      apply flatten_coercion; auto.
      apply (Prelude_error "RCast at level >0").

    destruct case_RJoin.
      simpl.
      destruct (getjlev x); destruct (getjlev q).
      apply nd_rule.
      apply RJoin.
      apply (Prelude_error "RJoin at depth >0").
      apply (Prelude_error "RJoin at depth >0").
      apply (Prelude_error "RJoin at depth >0").

    destruct case_RApp.
      simpl.

      destruct lev as [|ec lev]. simpl. apply nd_rule.
        replace (garrowfy_code_types  (tx ---> te)) with ((garrowfy_code_types  tx) ---> (garrowfy_code_types  te)).
        apply RApp.
        reflexivity.

        repeat drop_simplify.
          repeat take_simplify.
          rewrite mapOptionTree_distributes.
          set (mapOptionTree (garrowfy_leveled_code_types ) (drop_lev (ec :: lev) Σ₁)) as Σ₁'.
          set (mapOptionTree (garrowfy_leveled_code_types ) (drop_lev (ec :: lev) Σ₂)) as Σ₂'.
          set (take_lev (ec :: lev) Σ₁) as Σ₁''.
          set (take_lev (ec :: lev) Σ₂) as Σ₂''.
          replace (garrowfy_code_types  (tx ---> te)) with ((garrowfy_code_types  tx) ---> (garrowfy_code_types  te)).
          apply (Prelude_error "FIXME: ga_apply").
          reflexivity.
(*
  Notation "`  x" := (take_lev _ x) (at level 20).
  Notation "`` x" := (mapOptionTree unlev x) (at level 20).
  Notation "``` x" := ((drop_lev _ x)) (at level 20).
  Notation "!<[]> x" := (garrowfy_code_types _ x) (at level 1).
  Notation "!<[@]>" := (garrowfy_leveled_code_types _) (at level 1).
*)
    destruct case_RLet.
      apply (Prelude_error "FIXME: RLet").
(*
      simpl.
      destruct lev as [|ec lev]; simpl; [ apply nd_rule; apply RLet; auto | idtac ].
      destruct (Peano_dec.eq_nat_dec (Datatypes.length lev) n); [ idtac | apply nd_rule; apply RLet; auto ]; simpl.
      repeat drop_simplify.
      repeat take_simplify.
      rename σ₁ into a.
      rename σ₂ into b.
      rewrite mapOptionTree_distributes.
      rewrite mapOptionTree_distributes.
      set (mapOptionTree (garrowfy_leveled_code_types (S n)) (drop_lev (ec :: lev) Σ₁)) as A.
      set (take_lev (ec :: lev) Σ₁) as A'.
      set (mapOptionTree (garrowfy_leveled_code_types (S n)) (drop_lev (ec :: lev) Σ₂)) as B.
      set (take_lev (ec :: lev) Σ₂) as B'.
      simpl.

      eapply nd_comp.
      Focus 2.
      eapply nd_rule.
      eapply RLet.

      apply nd_prod.

      apply boost.
      apply ga_second.

      eapply nd_comp.
      Focus 2.
      eapply boost.
      apply ga_comp.

      eapply nd_comp.
      eapply nd_rule.
      eapply RArrange.
      eapply RCanR.

      eapply nd_comp.
      Focus 2.
      eapply nd_rule.
      eapply RArrange.
      eapply RExch.
      idtac.

      eapply nd_comp.
      apply nd_llecnac.
      eapply nd_comp.
      Focus 2.
      eapply nd_rule.
      apply RJoin.
      apply nd_prod.

      eapply nd_rule.
      eapply RVar.

      apply nd_id.
*)
    destruct case_RVoid.
      simpl.
      apply nd_rule.
      apply RVoid.
        
    destruct case_RAppT.
      simpl. destruct lev; simpl.
      rewrite garrowfy_commutes_with_HaskTAll.
      rewrite garrowfy_commutes_with_substT.
      apply nd_rule.
      apply RAppT.
      apply Δ.
      apply Δ.
      apply (Prelude_error "ga_apply").

    destruct case_RAbsT.
      simpl. destruct lev; simpl.
      rewrite garrowfy_commutes_with_HaskTAll.
      rewrite garrowfy_commutes_with_HaskTApp.
      eapply nd_comp; [ idtac | eapply nd_rule; eapply RAbsT ].
      simpl.
      set (mapOptionTree (garrowfy_leveled_code_types ) (mapOptionTree (weakLT(κ:=κ)) Σ)) as a.
      set (mapOptionTree (weakLT(κ:=κ)) (mapOptionTree (garrowfy_leveled_code_types ) Σ)) as q'.
      assert (a=q').
        unfold a.
        unfold q'.
        clear a q'.
        induction Σ.
          destruct a.
          simpl.
          rewrite garrowfy_commutes_with_weakLT.
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
      apply (Prelude_error "AbsT at depth>0").

    destruct case_RAppCo.
      simpl. destruct lev; simpl.
      unfold garrowfy_code_types.
      simpl.
      apply nd_rule.
      apply RAppCo.
      apply flatten_coercion.
      apply γ.
      apply (Prelude_error "AppCo at depth>0").

    destruct case_RAbsCo.
      simpl. destruct lev; simpl.
      unfold garrowfy_code_types.
      simpl.
      apply (Prelude_error "AbsCo not supported (FIXME)").
      apply (Prelude_error "AbsCo at depth>0").

    destruct case_RLetRec.
      rename t into lev.
      apply (Prelude_error "LetRec not supported (FIXME)").

    destruct case_RCase.
      simpl.
      apply (Prelude_error "Case not supported (FIXME)").
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
