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
Require Import NaturalDeductionContext.
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
                               in  ga_mk_raw ec (unleaves_ (take_arg_types e')) [drop_arg_types e']
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

  (* "n" is the maximum depth remaining AFTER flattening *)
  Definition flatten_judgment (j:Judg) :=
    match j as J return Judg with
      | Γ > Δ > ant |- suc @ nil        => Γ > Δ > mapOptionTree flatten_leveled_type ant
                                                |- mapOptionTree flatten_type suc @ nil
      | Γ > Δ > ant |- suc @ (ec::lev') => Γ > Δ > mapOptionTree flatten_leveled_type (drop_lev (ec::lev') ant)
                                                |- [ga_mk (v2t ec)
                                                  (mapOptionTree (flatten_type ○ unlev) (take_lev (ec::lev') ant))
                                                  (mapOptionTree  flatten_type                               suc )
                                                  ] @ nil
    end.

  Class garrow :=
  { ga_id        : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec a a ]@l ]
  ; ga_cancelr   : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec (a,,[]) a ]@l ]
  ; ga_cancell   : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec ([],,a) a ]@l ]
  ; ga_uncancelr : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec a (a,,[]) ]@l ]
  ; ga_uncancell : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec a ([],,a) ]@l ]
  ; ga_assoc     : ∀ Γ Δ ec l a b c, ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec ((a,,b),,c) (a,,(b,,c)) ]@l ]
  ; ga_unassoc   : ∀ Γ Δ ec l a b c, ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec (a,,(b,,c)) ((a,,b),,c) ]@l ]
  ; ga_swap      : ∀ Γ Δ ec l a b  , ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec (a,,b) (b,,a) ]@l ]
  ; ga_drop      : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec a [] ]@l ]
  ; ga_copy      : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec a (a,,a) ]@l ]
  ; ga_first     : ∀ Γ Δ ec l a b x, ND Rule [] [Γ > Δ >      [@ga_mk Γ ec a b @@l] |- [@ga_mk Γ ec (a,,x) (b,,x) ]@l ]
  ; ga_second    : ∀ Γ Δ ec l a b x, ND Rule [] [Γ > Δ >      [@ga_mk Γ ec a b @@l] |- [@ga_mk Γ ec (x,,a) (x,,b) ]@l ]
  ; ga_lit       : ∀ Γ Δ ec l lit  , ND Rule [] [Γ > Δ >                          [] |- [@ga_mk Γ ec [] [literalType lit] ]@l ]
  ; ga_curry     : ∀ Γ Δ ec l a b c, ND Rule [] [Γ > Δ > [@ga_mk Γ ec (a,,[b]) [c] @@ l] |- [@ga_mk Γ ec a [b ---> c] ]@ l ]
  ; ga_comp      : ∀ Γ Δ ec l a b c, ND Rule [] [Γ > Δ > [@ga_mk Γ ec a b @@ l],,[@ga_mk Γ ec b c @@ l] |- [@ga_mk Γ ec a c ]@l ] 
  ; ga_apply     : ∀ Γ Δ ec l a a' b c,
                 ND Rule [] [Γ > Δ > [@ga_mk Γ ec a [b ---> c] @@ l],,[@ga_mk Γ ec a' [b] @@ l] |- [@ga_mk Γ ec (a,,a') [c] ]@l ]
  ; ga_kappa     : ∀ Γ Δ ec l a b Σ, ND Rule
  [Γ > Δ > Σ,,[@ga_mk Γ ec [] a @@ l] |- [@ga_mk Γ ec [] b ]@l ]
  [Γ > Δ > Σ          |- [@ga_mk Γ ec a  b ]@l ]
  }.
  Context `(gar:garrow).

  Notation "a ~~~~> b" := (@ga_mk _ _ a b) (at level 20).

  Definition boost : forall Γ Δ ant x y {lev},
    ND Rule []                         [ Γ > Δ > [x@@lev] |- [y]@lev ] ->
    ND Rule [ Γ > Δ > ant |- [x]@lev ] [ Γ > Δ > ant      |- [y]@lev ].
    intros.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply ACanR ].
    eapply nd_comp; [ idtac | eapply nd_rule; apply RLet ].
    eapply nd_comp; [ apply nd_rlecnac | idtac ].
    apply nd_prod.
    apply nd_id.
    eapply nd_comp.
      apply X.
      eapply nd_rule.
      eapply RArrange.
      apply AuCanR.
    Defined.

  Definition precompose Γ Δ ec : forall a x y z lev,
    ND Rule
      [ Γ > Δ > a                           |- [@ga_mk _ ec y z ]@lev ]
      [ Γ > Δ > a,,[@ga_mk _ ec x y @@ lev] |- [@ga_mk _ ec x z ]@lev ].
    intros.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RLet ].
    eapply nd_comp; [ apply nd_rlecnac | idtac ].
    apply nd_prod.
    apply nd_id.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply AExch ].
    apply ga_comp.
    Defined.

  Definition precompose' Γ Δ ec : forall a b x y z lev,
    ND Rule
      [ Γ > Δ > a,,b                             |- [@ga_mk _ ec y z ]@lev ]
      [ Γ > Δ > a,,([@ga_mk _ ec x y @@ lev],,b) |- [@ga_mk _ ec x z ]@lev ].
    intros.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply ALeft; eapply AExch ].
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply AuAssoc ].
    apply precompose.
    Defined.

  Definition postcompose_ Γ Δ ec : forall a x y z lev,
    ND Rule
      [ Γ > Δ > a                           |- [@ga_mk _ ec x y ]@lev ]
      [ Γ > Δ > a,,[@ga_mk _ ec y z @@ lev] |- [@ga_mk _ ec x z ]@lev ].
    intros.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RLet ].
    eapply nd_comp; [ apply nd_rlecnac | idtac ].
    apply nd_prod.
    apply nd_id.
    apply ga_comp.
    Defined.

  Definition postcompose  Γ Δ ec : forall x y z lev,
    ND Rule [] [ Γ > Δ > []                       |- [@ga_mk _ ec x y ]@lev ] ->
    ND Rule [] [ Γ > Δ > [@ga_mk _ ec y z @@ lev] |- [@ga_mk _ ec x z ]@lev ].
    intros.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply ACanL ].
    eapply nd_comp; [ idtac | eapply postcompose_ ].
    apply X.
    Defined.

  Definition first_nd : ∀ Γ Δ ec lev a b c Σ,
    ND Rule [ Γ > Δ > Σ                    |- [@ga_mk Γ ec a b ]@lev ]
            [ Γ > Δ > Σ                    |- [@ga_mk Γ ec (a,,c) (b,,c) ]@lev ].
    intros.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply ACanR ].
    eapply nd_comp; [ idtac | eapply nd_rule; apply RLet ].
    eapply nd_comp; [ apply nd_rlecnac | idtac ].
    apply nd_prod.
    apply nd_id.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply AuCanR ].
    apply ga_first.
    Defined.

  Definition firstify : ∀ Γ Δ ec lev a b c Σ,
    ND Rule [] [ Γ > Δ > Σ                    |- [@ga_mk Γ ec a b ]@lev ] ->
    ND Rule [] [ Γ > Δ > Σ                    |- [@ga_mk Γ ec (a,,c) (b,,c) ]@lev ].
    intros.
    eapply nd_comp.
    apply X.
    apply first_nd.
    Defined.

  Definition second_nd : ∀ Γ Δ ec lev a b c Σ,
     ND Rule
     [ Γ > Δ > Σ                    |- [@ga_mk Γ ec a b ]@lev ]
     [ Γ > Δ > Σ                    |- [@ga_mk Γ ec (c,,a) (c,,b) ]@lev ].
    intros.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply ACanR ].
    eapply nd_comp; [ idtac | eapply nd_rule; apply RLet ].
    eapply nd_comp; [ apply nd_rlecnac | idtac ].
    apply nd_prod.
    apply nd_id.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply AuCanR ].
    apply ga_second.
    Defined.

  Definition secondify : ∀ Γ Δ ec lev a b c Σ,
     ND Rule [] [ Γ > Δ > Σ                    |- [@ga_mk Γ ec a b ]@lev ] ->
     ND Rule [] [ Γ > Δ > Σ                    |- [@ga_mk Γ ec (c,,a) (c,,b) ]@lev ].
    intros.
    eapply nd_comp.
    apply X.
    apply second_nd.
    Defined.

   Lemma ga_unkappa     : ∀ Γ Δ ec l a b Σ x,
     ND Rule
     [Γ > Δ > Σ                          |- [@ga_mk Γ ec (a,,x)  b ]@l ] 
     [Γ > Δ > Σ,,[@ga_mk Γ ec [] a @@ l] |- [@ga_mk Γ ec x       b ]@l ].
     intros.
     eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply AExch ].
     eapply nd_comp; [ idtac | eapply nd_rule; eapply RLet ].
     eapply nd_comp; [ apply nd_llecnac | idtac ].
     apply nd_prod.
     apply ga_first.

     eapply nd_comp; [ idtac | eapply nd_rule; eapply RLet ].
     eapply nd_comp; [ apply nd_llecnac | idtac ].
     apply nd_prod.
     apply postcompose.
     apply ga_uncancell.
     eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply AExch ].
     apply precompose.
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
        (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) ant1)) ]@nil ].

      intros Γ Δ ec lev.
      refine (fix flatten ant1 ant2 (r:Arrange ant1 ant2):
           ND Rule [] [Γ > Δ > [] |- [@ga_mk _ (v2t ec)
             (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) ant2))
             (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) ant1)) ]@nil] :=
        match r as R in Arrange A B return
          ND Rule [] [Γ > Δ > [] |- [@ga_mk _ (v2t ec)
            (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) B))
            (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) A)) ]@nil]
          with
          | AId  a               => let case_AId := tt    in ga_id _ _ _ _ _
          | ACanL  a             => let case_ACanL := tt  in ga_uncancell _ _ _ _ _
          | ACanR  a             => let case_ACanR := tt  in ga_uncancelr _ _ _ _ _
          | AuCanL a             => let case_AuCanL := tt in ga_cancell _ _ _ _ _
          | AuCanR a             => let case_AuCanR := tt in ga_cancelr _ _ _ _ _
          | AAssoc a b c         => let case_AAssoc := tt in ga_assoc _ _ _ _ _ _ _
          | AuAssoc a b c         => let case_AuAssoc := tt in ga_unassoc _ _ _ _ _ _ _
          | AExch  a b           => let case_AExch := tt  in ga_swap  _ _ _ _ _ _
          | AWeak  a             => let case_AWeak := tt  in ga_drop _ _ _ _ _ 
          | ACont  a             => let case_ACont := tt  in ga_copy  _ _ _ _ _ 
          | ALeft  a b c r'      => let case_ALeft := tt  in flatten _ _ r' ;; boost _ _ _ _ _ (ga_second _ _ _ _ _ _ _)
          | ARight a b c r'      => let case_ARight := tt in flatten _ _ r' ;; boost _ _ _ _ _ (ga_first  _ _ _ _ _ _ _)
          | AComp  c b a r1 r2   => let case_AComp := tt  in (fun r1' r2' => _) (flatten _ _ r1) (flatten _ _ r2)
        end); clear flatten; repeat take_simplify; repeat drop_simplify; intros.

        destruct case_AComp.
          set (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) a)) as a' in *.
          set (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) b)) as b' in *.
          set (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) c)) as c' in *.
          eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; apply ACanL ].
          eapply nd_comp; [ idtac | eapply nd_rule; apply
             (@RLet Γ Δ [] [] (@ga_mk _ (v2t ec) a' b') (@ga_mk _ (v2t ec) a' c')) ].
          eapply nd_comp; [ apply nd_llecnac | idtac ].
          apply nd_prod.
          apply r2'.
          eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; apply AuCanR ].
          eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; apply ACanL ].
          eapply nd_comp; [ idtac | eapply nd_rule;  apply RLet ].
          eapply nd_comp; [ apply nd_llecnac | idtac ].
          eapply nd_prod.
          apply r1'.
          eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply AExch ].
          apply ga_comp.
          Defined.

  Definition flatten_arrangement :
    forall Γ (Δ:CoercionEnv Γ) n
      (ec:HaskTyVar Γ ECKind) (lev:HaskLevel Γ) (ant1 ant2:Tree ??(LeveledHaskType Γ ★)) (r:Arrange ant1 ant2) succ,
      ND Rule
      [Γ > Δ > mapOptionTree (flatten_leveled_type ) (drop_lev n ant1)
        |- [@ga_mk _ (v2t ec)
          (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) ant1))
          (mapOptionTree (flatten_type ) succ) ]@nil]
      [Γ > Δ > mapOptionTree (flatten_leveled_type ) (drop_lev n ant2)
        |- [@ga_mk _ (v2t ec)
          (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) ant2))
          (mapOptionTree (flatten_type ) succ) ]@nil].
      intros.
      refine ( _ ;; (boost _ _ _ _ _ (postcompose _ _ _ _ _ _ _ (flatten_arrangement' Γ Δ ec lev ant1 ant2 r)))).
      apply nd_rule.
      apply RArrange.
      refine ((fix flatten ant1 ant2 (r:Arrange ant1 ant2) :=
        match r as R in Arrange A B return
          Arrange (mapOptionTree (flatten_leveled_type ) (drop_lev _ A))
          (mapOptionTree (flatten_leveled_type ) (drop_lev _ B)) with
          | AId  a               => let case_AId := tt  in AId _
          | ACanL  a             => let case_ACanL := tt  in ACanL _
          | ACanR  a             => let case_ACanR := tt  in ACanR _
          | AuCanL a             => let case_AuCanL := tt in AuCanL _
          | AuCanR a             => let case_AuCanR := tt in AuCanR _
          | AAssoc a b c         => let case_AAssoc := tt in AAssoc _ _ _
          | AuAssoc a b c         => let case_AuAssoc := tt in AuAssoc _ _ _
          | AExch  a b           => let case_AExch := tt  in AExch _ _
          | AWeak  a             => let case_AWeak := tt  in AWeak _
          | ACont  a             => let case_ACont := tt  in ACont _
          | ALeft  a b c r'      => let case_ALeft := tt  in ALeft  _ (flatten _ _ r')
          | ARight a b c r'      => let case_ARight := tt in ARight _ (flatten _ _ r')
          | AComp  a b c r1 r2   => let case_AComp := tt  in AComp    (flatten _ _ r1) (flatten _ _ r2)
        end) ant1 ant2 r); clear flatten; repeat take_simplify; repeat drop_simplify; intros.
        Defined.

  Definition flatten_arrangement'' :
    forall  Γ Δ ant1 ant2 succ l (r:Arrange ant1 ant2),
      ND Rule (mapOptionTree (flatten_judgment ) [Γ > Δ > ant1 |- succ @ l])
      (mapOptionTree (flatten_judgment ) [Γ > Δ > ant2 |- succ @ l]).
    intros.
    simpl.
    destruct l.
      apply nd_rule.
      apply RArrange.
      induction r; simpl.
        apply AId.
        apply ACanL.
        apply ACanR.
        apply AuCanL.
        apply AuCanR.
        apply AAssoc.
        apply AuAssoc.
        apply AExch.    (* TO DO: check for all-leaf trees here *)
        apply AWeak.
        apply ACont.
        apply ALeft; auto.
        apply ARight; auto.
        eapply AComp; [ apply IHr1 | apply IHr2 ].

      apply flatten_arrangement.
        apply r.
        Defined.

  Definition ga_join Γ Δ Σ₁ Σ₂ a b ec :
    ND Rule [] [Γ > Δ > Σ₁     |- [@ga_mk _ ec [] a      ]@nil] ->
    ND Rule [] [Γ > Δ > Σ₂     |- [@ga_mk _ ec [] b      ]@nil] ->
    ND Rule [] [Γ > Δ > Σ₁,,Σ₂ |- [@ga_mk _ ec [] (a,,b) ]@nil].
    intro pfa.
    intro pfb.
    apply secondify with (c:=a)  in pfb.
    apply firstify  with (c:=[])  in pfa.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RLet ].
    eapply nd_comp; [ eapply nd_llecnac | idtac ].
    apply nd_prod.
    apply pfa.
    clear pfa.

    eapply nd_comp; [ idtac | eapply nd_rule; eapply RLet ].
    eapply nd_comp; [ apply nd_llecnac | idtac ].
    apply nd_prod.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply ACanL ].
    eapply nd_comp; [ idtac | eapply postcompose_ ].
    apply ga_uncancelr.

    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply AExch ].
    eapply nd_comp; [ idtac | eapply precompose ].
    apply pfb.
    Defined.

  Definition arrange_brak : forall Γ Δ ec succ t,
   ND Rule
     [Γ > Δ > 
      [(@ga_mk _ (v2t ec) [] (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: nil) succ))) @@  nil],,
      mapOptionTree (flatten_leveled_type ) (drop_lev (ec :: nil) succ) |- [t]@nil]
     [Γ > Δ > mapOptionTree (flatten_leveled_type ) succ |- [t]@nil].

    intros.
    unfold drop_lev.
    set (@arrangeUnPartition _ succ (levelMatch (ec::nil))) as q.
    set (arrangeMap _ _ flatten_leveled_type q) as y.
    eapply nd_comp.
    Focus 2.
    eapply nd_rule.
    eapply RArrange.
    apply y.
    idtac.
    clear y q.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply AExch ].
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
     [Γ > Δ > mapOptionTree (flatten_leveled_type ) succ |- [t]@nil]
     [Γ > Δ > 
      [(@ga_mk _ (v2t ec) [] (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: nil) succ))) @@  nil],,
      mapOptionTree (flatten_leveled_type ) (drop_lev (ec :: nil) succ)  |- [t]@nil].
    intros.
    set (@arrangePartition _ succ (levelMatch (ec::nil))) as q.
    set (@drop_lev Γ (ec::nil) succ) as q'.
    assert (@drop_lev Γ (ec::nil) succ=q') as H.
      reflexivity.
    unfold drop_lev in H.
    unfold mkDropFlags in H.
    rewrite H in q.
    clear H.
    set (arrangeMap _ _ flatten_leveled_type q) as y.
    eapply nd_comp.
    eapply nd_rule.
    eapply RArrange.
    apply y.
    clear y q.

    set (mapOptionTree flatten_leveled_type (dropT (mkFlags (liftBoolFunc false (bnot ○ levelMatch (ec :: nil))) succ))) as q.
    destruct (decide_tree_empty q); [ idtac | apply (Prelude_error "escapifying open code not yet supported") ].
    destruct s.

    simpl.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; apply AExch ].
    set (fun z z' => @RLet Γ Δ z (mapOptionTree flatten_leveled_type q') t z' nil) as q''.
    eapply nd_comp; [ idtac | eapply nd_rule; apply RLet ].
    clear q''.
    eapply nd_comp; [ apply nd_rlecnac | idtac ].
    apply nd_prod.
    apply nd_rule.
    apply RArrange.
    eapply AComp; [ idtac | apply ACanR ].
    apply ALeft.
    apply (@arrangeCancelEmptyTree _ _ _ _ e).
   
    eapply nd_comp.
      eapply nd_rule.
      eapply (@RVar Γ Δ t nil).
    apply nd_rule.
      apply RArrange.
      eapply AComp.
      apply AuCanR.
      apply ALeft.
      apply AWeak.
(*
    eapply decide_tree_empty.

    simpl.
    set (dropT (mkFlags (liftBoolFunc false (bnot ○ levelMatch (ec :: nil))) succ)) as escapified.
    destruct (decide_tree_empty escapified).

    induction succ.
    destruct a.
      unfold drop_lev.
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
        apply ALeft.
        apply AWeak.
      simpl.
        apply nd_rule.
        unfold take_lev.
        simpl.
        apply RArrange.
        apply ALeft.
        apply AWeak.
      apply (Prelude_error "escapifying code with multi-leaf antecedents is not supported").
*)
      Defined.

  Lemma unlev_relev : forall {Γ}(t:Tree ??(HaskType Γ ★)) lev, mapOptionTree unlev (t @@@ lev) = t.
    intros.
    induction t.
    destruct a; reflexivity.
    rewrite <- IHt1 at 2.
    rewrite <- IHt2 at 2.
    reflexivity.
    Qed.

  Lemma tree_of_nothing : forall Γ ec t,
    Arrange (mapOptionTree flatten_leveled_type (drop_lev(Γ:=Γ) (ec :: nil) (t @@@ (ec :: nil)))) [].
    intros.
    induction t; try destruct o; try destruct a.
    simpl.
    drop_simplify.
    simpl.
    apply AId.
    simpl.
    apply AId.
    eapply AComp; [ idtac | apply ACanL ].
    eapply AComp; [ idtac | eapply ALeft; apply IHt2 ].
    Opaque drop_lev.
    simpl.
    Transparent drop_lev.
    idtac.
    drop_simplify.
    apply ARight.
    apply IHt1.
    Defined.

  Lemma tree_of_nothing' : forall Γ ec t,
    Arrange [] (mapOptionTree flatten_leveled_type (drop_lev(Γ:=Γ) (ec :: nil) (t @@@ (ec :: nil)))).
    intros.
    induction t; try destruct o; try destruct a.
    simpl.
    drop_simplify.
    simpl.
    apply AId.
    simpl.
    apply AId.
    eapply AComp; [ apply AuCanL | idtac ].
    eapply AComp; [ eapply ARight; apply IHt1 | idtac ].
    Opaque drop_lev.
    simpl.
    Transparent drop_lev.
    idtac.
    drop_simplify.
    apply ALeft.
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
    apply phoas_extensionality.
    intros.
    unfold v2t.
    unfold ga_mk_raw.
    unfold ga_mk_tree.
    rewrite <- mapOptionTree_compose.
    unfold take_arg_types_as_tree.
    simpl.
    replace (flatten_type (drop_arg_types_as_tree t) tv ite)
      with (drop_arg_types (flatten_rawtype (t tv ite))).
    replace (unleaves_ (take_arg_types (flatten_rawtype (t tv ite))))
      with ((mapOptionTree (fun x : HaskType Γ ★ => flatten_type x tv ite)
           (unleaves_
              (take_trustme (count_arg_types (t (fun _ : Kind => unit) (ite_unit Γ)))
                 (fun TV : Kind → Type => take_arg_types ○ t TV))))).
    reflexivity.
    unfold flatten_type.
    clear hetmet_flatten.
    clear hetmet_unflatten.
    clear hetmet_id.
    clear gar.
    set (t tv ite) as x.
    admit.
    admit.
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
      | RArrange Γ Δ a b x l d         => let case_RArrange := tt      in _
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
      | RWhere   Γ Δ Σ₁ Σ₂ Σ₃ σ₁ σ₂ lev   => let case_RWhere := tt          in _
      | RJoin    Γ p lri m x q l       => let case_RJoin := tt in _
      | RVoid    _ _       l           => let case_RVoid := tt   in _
      | RBrak    Γ Δ t ec succ lev           => let case_RBrak := tt         in _
      | REsc     Γ Δ t ec succ lev           => let case_REsc := tt          in _
      | RCase    Γ Δ lev tc Σ avars tbranches alts => let case_RCase := tt         in _
      | RLetRec  Γ Δ lri x y t         => let case_RLetRec := tt       in _
      end); clear X h c.

    destruct case_RArrange.
      apply (flatten_arrangement''  Γ Δ a b x _ d).

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
        apply ACanR.
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
      destruct l;
        [ apply nd_rule; apply RJoin | idtac ];
        apply (Prelude_error "RJoin at depth >0").

    destruct case_RApp.
      simpl.

      destruct lev as [|ec lev].
        unfold flatten_type at 1.
        simpl.
        apply nd_rule.
        apply RApp.

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

      set (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) Σ₁)) as Σ₁'.
      set (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) Σ₂)) as Σ₂'.
      set (mapOptionTree flatten_leveled_type (drop_lev (ec :: lev) Σ₁)) as Σ₁''.
      set (mapOptionTree flatten_leveled_type (drop_lev (ec :: lev) Σ₂)) as Σ₂''.

      eapply nd_comp.
      eapply nd_prod; [ idtac | apply nd_id ].
      eapply boost.
      apply (ga_first _ _ _ _ _ _ Σ₂').

      eapply nd_comp; [ idtac | eapply nd_rule; eapply RLet ].
      apply nd_prod.
      apply nd_id.
      eapply nd_comp; [ eapply nd_rule; eapply RArrange; eapply ACanL | idtac ].
      eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply AExch (* okay *)].
      apply precompose.

    destruct case_RWhere.
      simpl.
      destruct lev as [|ec lev]; simpl; [ apply nd_rule; apply RWhere; auto | idtac ].
      repeat take_simplify.
      repeat drop_simplify.
      simpl.

      set (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) Σ₁)) as Σ₁'.
      set (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) Σ₂)) as Σ₂'.
      set (mapOptionTree (flatten_type ○ unlev) (take_lev (ec :: lev) Σ₃)) as Σ₃'.
      set (mapOptionTree flatten_leveled_type (drop_lev (ec :: lev) Σ₁)) as Σ₁''.
      set (mapOptionTree flatten_leveled_type (drop_lev (ec :: lev) Σ₂)) as Σ₂''.
      set (mapOptionTree flatten_leveled_type (drop_lev (ec :: lev) Σ₃)) as Σ₃''.

      eapply nd_comp.
      eapply nd_prod; [ eapply nd_id | idtac ].
      eapply (first_nd _ _ _ _ _ _ Σ₃').
      eapply nd_comp.
      eapply nd_prod; [ eapply nd_id | idtac ].
      eapply (second_nd _ _ _ _ _ _ Σ₁').

      eapply nd_comp; [ idtac | eapply nd_rule; eapply RWhere ].
      apply nd_prod; [ idtac | apply nd_id ].
      eapply nd_comp; [ idtac | eapply precompose' ].
      apply nd_rule.
      apply RArrange.
      apply ALeft.
      apply ACanL.

    destruct case_RVoid.
      simpl.
      apply nd_rule.
      destruct l.
      apply RVoid.
      apply (Prelude_error "RVoid at level >0").
        
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
      simpl. destruct lev; simpl.
      apply nd_rule.
      set (@RLetRec Γ Δ (mapOptionTree flatten_leveled_type lri) (flatten_type x) (mapOptionTree flatten_type y) nil) as q.
      replace (mapOptionTree flatten_leveled_type (y @@@ nil)) with (mapOptionTree flatten_type y @@@ nil).
      apply q.
        induction y; try destruct a; auto.
        simpl.
        rewrite IHy1.
        rewrite IHy2.
        reflexivity.
      apply (Prelude_error "LetRec not supported inside brackets yet (FIXME)").

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
      simpl.
      rewrite krunk.
      set (mapOptionTree flatten_leveled_type (drop_lev (ec :: nil) succ)) as succ_host.
      set (mapOptionTree (flatten_type ○ unlev)(take_lev (ec :: nil) succ)) as succ_guest.
      set (mapOptionTree flatten_type (take_arg_types_as_tree t)) as succ_args.
      unfold empty_tree.
      eapply nd_comp; [ eapply nd_rule; eapply RArrange; eapply ALeft; apply tree_of_nothing | idtac ].
      eapply nd_comp; [ eapply nd_rule; eapply RArrange; eapply ACanR | idtac ].
      refine (ga_unkappa Γ Δ (v2t ec) nil _ _ _ _ ;; _).
      eapply nd_comp; [ idtac | eapply arrange_brak ].
      unfold succ_host.
      unfold succ_guest.
      eapply nd_rule.
        eapply RArrange.
        apply AExch.
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
      eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply ALeft; apply tree_of_nothing' ].
      eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply ACanR ].
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

      eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; apply AuCanR ].
      eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; apply AuCanR ].
      eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; apply ACanL ].
      eapply nd_comp; [ idtac | eapply nd_rule; eapply RLet ].
      eapply nd_comp; [ apply nd_llecnac | idtac ].
      apply nd_prod; [ idtac | eapply boost ].
      induction x.
        apply ga_id.
        eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply ACanL ].
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
      apply (Prelude_error "ga_kappa not supported yet (BIG FIXME)").

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
