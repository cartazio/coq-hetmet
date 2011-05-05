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
Require Import BinoidalCategories.
Require Import PreMonoidalCategories.
Require Import MonoidalCategories_ch7_8.
Require Import Coherence_ch7_8.

Require Import HaskStrongTypes.
Require Import HaskStrong.
Require Import HaskProof.
Require Import HaskStrongToProof.
Require Import HaskProofToStrong.
Require Import ProgrammingLanguage.
Require Import HaskProgrammingLanguage.
Require Import PCF.

Open Scope nd_scope.

(*
 *  The flattening transformation.  Currently only TWO-level languages are
 *  supported, and the level-1 sublanguage is rather limited.
 *
 *  This file abuses terminology pretty badly.  For purposes of this file,
 *  "PCF" means "the level-1 sublanguage" and "FC" (aka System FC) means 
 *  the whole language (level-0 language including bracketed level-1 terms)
 *)
Section HaskFlattener.

  (* this actually has nothing to do with categories; it shows that proofs [|-A]//[|-B] are one-to-one with []//[A|-B] *)
  (* TODO Lemma hom_functor_full*)

  (* lemma: if a proof from no hypotheses contains no Brak's or Esc's, then the context contains no variables at level!=0 *)

  Definition minus' n m :=
    match m with
      | 0 => n
      | _ => match n with
               | 0 => 0
               | _ => n - m
             end
    end.

  Ltac eqd_dec_refl' :=
    match goal with
      | [ |- context[@eqd_dec ?T ?V ?X ?X] ] =>
        destruct (@eqd_dec T V X X) as [eqd_dec1 | eqd_dec2];
          [ clear eqd_dec1 | set (eqd_dec2 (refl_equal _)) as eqd_dec2'; inversion eqd_dec2' ]
  end.

  (* The opposite: replace any type which is NOT at level "lev" with None *)
  Definition take_lev {Γ}(lev:HaskLevel Γ)(tt:Tree ??(LeveledHaskType Γ ★)) : Tree ??(HaskType Γ ★) :=
    mapTree (fun t => match t with
                        | Some (ttype @@ tlev) => if eqd_dec tlev lev then Some ttype else None
                        | _                    => None
                      end) tt.

  (* In a tree of types, replace any type at depth "lev" or greater None *)
  Definition drop_depth {Γ}(lev:HaskLevel Γ)(tt:Tree ??(LeveledHaskType Γ ★)) : Tree ??(LeveledHaskType Γ ★) :=
    mapTree (fun t => match t with
                        | Some (ttype @@ tlev) => if eqd_dec tlev lev then None else t
                        | _ => t
                      end) tt.

  Lemma drop_depth_lemma : forall Γ (lev:HaskLevel Γ) x, drop_depth lev [x @@  lev] = [].
    intros; simpl.
    Opaque eqd_dec.
    unfold drop_depth.
    simpl.
    Transparent eqd_dec.
    eqd_dec_refl'.
    auto.
    Qed.

  Lemma drop_depth_lemma_s : forall Γ (lev:HaskLevel Γ) ec x, drop_depth (ec::lev) [x @@  (ec :: lev)] = [].
    intros; simpl.
    Opaque eqd_dec.
    unfold drop_depth.
    simpl.
    Transparent eqd_dec.
    eqd_dec_refl'.
    auto.
    Qed.

  Lemma take_lemma : forall Γ (lev:HaskLevel Γ) x, take_lev lev [x @@  lev] = [x].
    intros; simpl.
    Opaque eqd_dec.
    unfold take_lev.
    simpl.
    Transparent eqd_dec.
    eqd_dec_refl'.
    auto.
    Qed.

  Ltac drop_simplify :=
    match goal with
      | [ |- context[@drop_depth ?G ?L [ ?X @@ ?L ] ] ] =>
        rewrite (drop_depth_lemma G L X)
      | [ |- context[@drop_depth ?G (?E :: ?L) [ ?X @@ (?E :: ?L) ] ] ] =>
        rewrite (drop_depth_lemma_s G L E X)
      | [ |- context[@drop_depth ?G ?N (?A,,?B)] ] =>
      change (@drop_depth G N (A,,B)) with ((@drop_depth G N A),,(@drop_depth G N B))
      | [ |- context[@drop_depth ?G ?N (T_Leaf None)] ] =>
      change (@drop_depth G N (T_Leaf (@None (LeveledHaskType G ★)))) with (T_Leaf (@None (LeveledHaskType G ★)))
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

  Fixpoint reduceTree {T}(unit:T)(merge:T -> T -> T)(tt:Tree ??T) : T :=
    match tt with
      | T_Leaf None     => unit
      | T_Leaf (Some x) => x
      | T_Branch b1 b2  => merge (reduceTree unit merge b1) (reduceTree unit merge b2)
    end.

  Set Printing Width 130.

  Context {unitTy : forall TV, RawHaskType TV  ★             }.
  Context {prodTy : forall TV, RawHaskType TV (★ ⇛ ★ ⇛ ★)    }.
  Context {gaTy   : forall TV, RawHaskType TV (★ ⇛ ★ ⇛ ★ ⇛ ★)}.

  Definition ga_tree      := fun TV tr => reduceTree (unitTy TV) (fun t1 t2 => TApp (TApp (prodTy TV) t1) t2) tr.
  Definition ga'          := fun TV ec ant' suc' => TApp (TApp (TApp (gaTy TV) ec) (ga_tree TV ant')) (ga_tree TV suc').
  Definition ga {Γ} : HaskType Γ ★ -> Tree ??(HaskType Γ ★) -> Tree ??(HaskType Γ ★) -> HaskType Γ ★ :=
    fun ec ant suc =>
                               fun TV ite =>
                                 let ant' := mapOptionTree (fun x => x TV ite) ant in
                                   let suc' := mapOptionTree (fun x => x TV ite) suc in
                                     ga' TV (ec TV ite) ant' suc'.

  Class garrow :=
  { ga_id        : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                           [] |- [@ga Γ ec a a @@ l] ]
  ; ga_cancelr   : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                           [] |- [@ga Γ ec (a,,[]) a @@ l] ]
  ; ga_cancell   : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                           [] |- [@ga Γ ec ([],,a) a @@ l] ]
  ; ga_uncancelr : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                           [] |- [@ga Γ ec a (a,,[]) @@ l] ]
  ; ga_uncancell : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                           [] |- [@ga Γ ec a ([],,a) @@ l] ]
  ; ga_assoc     : ∀ Γ Δ ec l a b c, ND Rule [] [Γ > Δ >                           [] |- [@ga Γ ec ((a,,b),,c) (a,,(b,,c)) @@ l] ]
  ; ga_unassoc   : ∀ Γ Δ ec l a b c, ND Rule [] [Γ > Δ >                           [] |- [@ga Γ ec (a,,(b,,c)) ((a,,b),,c) @@ l] ]
  ; ga_swap      : ∀ Γ Δ ec l a b  , ND Rule [] [Γ > Δ >                           [] |- [@ga Γ ec (a,,b) (b,,a) @@ l] ]
  ; ga_drop      : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                           [] |- [@ga Γ ec a [] @@ l] ]
  ; ga_copy      : ∀ Γ Δ ec l a    , ND Rule [] [Γ > Δ >                           [] |- [@ga Γ ec a (a,,a) @@ l] ]
  ; ga_first     : ∀ Γ Δ ec l a b x, ND Rule [] [Γ > Δ >          [@ga Γ ec a b @@ l] |- [@ga Γ ec (a,,x) (b,,x) @@ l] ]
  ; ga_second    : ∀ Γ Δ ec l a b x, ND Rule [] [Γ > Δ >          [@ga Γ ec a b @@ l] |- [@ga Γ ec (x,,a) (x,,b) @@ l] ]
  ; ga_lit       : ∀ Γ Δ ec l lit  , ND Rule [] [Γ > Δ >                           [] |- [@ga Γ ec [] [literalType lit] @@ l] ]
  ; ga_curry     : ∀ Γ Δ ec l a b c, ND Rule [] [Γ > Δ > [@ga Γ ec (a,,[b]) [c] @@ l] |- [@ga Γ ec a [b ---> c] @@ l] ]
  ; ga_comp      : ∀ Γ Δ ec l a b c, ND Rule [] [Γ > Δ > [@ga Γ ec a b @@ l],,[@ga Γ ec b c @@ l] |- [@ga Γ ec a c @@ l] ] 
  ; ga_apply     : ∀ Γ Δ ec l a a' b c, ND Rule []
                                  [Γ > Δ > [@ga Γ ec a [b ---> c] @@ l],,[@ga Γ ec a' [b] @@ l] |- [@ga Γ ec (a,,a') [c] @@ l] ]
  ; ga_kappa     : ∀ Γ Δ ec l a b Σ, ND Rule
  [Γ > Δ > Σ,,[@ga Γ ec [] a @@ l] |- [@ga Γ ec [] b @@ l] ]
  [Γ > Δ > Σ          |- [@ga Γ ec a  b @@ l] ]
  }.
  Context `(gar:garrow).

  Notation "a ~~~~> b" := (@ga _ _ a b) (at level 20).

  (*
   *  The story:
   *    - code types <[t]>@c                                                become garrows  c () t 
   *    - free variables of type t at a level lev deeper than the succedent become garrows  c () t
   *    - free variables at the level of the succedent become 
   *)
  Fixpoint garrowfy_raw_codetypes {TV}{κ}(depth:nat)(exp: RawHaskType TV κ) : RawHaskType TV κ :=
    match exp with
    | TVar    _  x        => TVar x
    | TAll     _ y        => TAll   _  (fun v => garrowfy_raw_codetypes depth (y v))
    | TApp   _ _ x y      => TApp      (garrowfy_raw_codetypes depth x) (garrowfy_raw_codetypes depth y)
    | TCon       tc       => TCon      tc
    | TCoerc _ t1 t2 t    => TCoerc    (garrowfy_raw_codetypes depth t1) (garrowfy_raw_codetypes depth t2)
                                       (garrowfy_raw_codetypes depth t)
    | TArrow              => TArrow
    | TCode      v e      => match depth with
                               | O          => ga' TV v [] [(*garrowfy_raw_codetypes depth*) e]
                               | (S depth') => TCode v (garrowfy_raw_codetypes depth' e)
                             end
    | TyFunApp     tfc lt => TyFunApp tfc (garrowfy_raw_codetypes_list _ depth lt)
    end
    with garrowfy_raw_codetypes_list {TV}(lk:list Kind)(depth:nat)(exp:@RawHaskTypeList TV lk) : @RawHaskTypeList TV lk :=
    match exp in @RawHaskTypeList _ LK return @RawHaskTypeList TV LK with
    | TyFunApp_nil               => TyFunApp_nil
    | TyFunApp_cons  κ kl t rest => TyFunApp_cons _ _ (garrowfy_raw_codetypes depth t) (garrowfy_raw_codetypes_list _ depth rest)
    end.
  Definition garrowfy_code_types {Γ}{κ}(n:nat)(ht:HaskType Γ κ) : HaskType Γ κ :=
    fun TV ite =>
      garrowfy_raw_codetypes n (ht TV ite).
  Definition garrowfy_leveled_code_types {Γ}(n:nat)(ht:LeveledHaskType Γ ★) : LeveledHaskType Γ ★ :=
    match ht with htt @@ htlev => garrowfy_code_types (minus' n (length htlev)) htt @@ htlev end.

  Axiom literal_types_unchanged : forall n Γ l, garrowfy_code_types n (literalType l) = literalType(Γ:=Γ) l.

  Axiom flatten_coercion : forall n Γ Δ κ (σ τ:HaskType Γ κ) (γ:HaskCoercion Γ Δ (σ ∼∼∼ τ)),
    HaskCoercion Γ Δ (garrowfy_code_types n σ ∼∼∼ garrowfy_code_types n τ).

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

  Definition v2t {Γ}(ec:HaskTyVar Γ ★) := fun TV ite => TVar (ec TV ite).

  (* "n" is the maximum depth remaining AFTER flattening *)
  Definition flatten_judgment (n:nat)(j:Judg) :=
    match j as J return Judg with
      Γ > Δ > ant |- suc =>
        match (match getjlev suc with
                 | nil        => inl _ tt
                 | (ec::lev') => if eqd_dec (length lev') n
                                 (* If the judgment's level is the deepest in the proof, flatten it by turning
                                  * all antecedent variables at this level into None's, garrowfying any other
                                  * antecedent variables (from other levels) at the same depth, and turning the
                                  * succedent into a garrow type *)
                                 then inr _ (Γ > Δ > mapOptionTree (garrowfy_leveled_code_types n) (drop_depth (ec::lev') ant)
                                                  |- [ga (v2t ec) (take_lev (ec::lev') ant) (mapOptionTree unlev suc) @@ lev'])
                                 else inl _ tt
               end) with

        (* otherwise, just garrowfy all code types of the specified depth, throughout the judgment *)
        | inl tt => Γ > Δ > mapOptionTree (garrowfy_leveled_code_types n) ant |- mapOptionTree (garrowfy_leveled_code_types n) suc
        | inr r => r
        end
    end.

  Definition boost : forall Γ Δ ant x y,
     ND Rule []                   [ Γ > Δ > x   |- y ] ->
     ND Rule [ Γ > Δ > ant |- x ] [ Γ > Δ > ant |- y ].
     admit.
     Defined.

  Definition postcompose : ∀ Γ Δ ec lev a b c,
     ND Rule [] [ Γ > Δ > []                    |- [@ga Γ ec a b @@ lev] ] ->
     ND Rule [] [ Γ > Δ > [@ga Γ ec b c @@ lev] |- [@ga Γ ec a c @@ lev] ].
     admit.
     Defined.

  Definition seq : ∀ Γ Δ lev a b,
     ND Rule [] [ Γ > Δ > [] |- [a @@ lev] ] ->
     ND Rule [] [ Γ > Δ > [] |- [b @@ lev] ] ->
     ND Rule [] [ Γ > Δ > [] |- [a @@ lev],,[b @@ lev] ].
     admit.
     Defined.

  Lemma ga_unkappa     : ∀ Γ Δ ec l a b Σ,
    ND Rule
    [Γ > Δ > Σ |- [@ga Γ ec a  b @@ l] ] 
    [Γ > Δ > Σ,,[@ga Γ ec [] a @@ l] |- [@ga Γ ec [] b @@ l] ].
    intros.
    set (ga_comp Γ Δ ec l [] a b) as q.

    set (@RLet Γ Δ) as q'.
    set (@RLet Γ Δ [@ga _ ec [] a @@ l] Σ (@ga _ ec [] b) (@ga _ ec a b) l) as q''.
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

(*
  Notation "`  x" := (take_lev _ x) (at level 20).
  Notation "`` x" := (mapOptionTree unlev x) (at level 20).
  Notation "``` x" := (drop_depth _ x) (at level 20).
*)
  Definition garrowfy_arrangement' :
    forall Γ (Δ:CoercionEnv Γ)
      (ec:HaskTyVar Γ ★) (lev:HaskLevel Γ) (ant1 ant2:Tree ??(LeveledHaskType Γ ★)) (r:Arrange ant1 ant2),
      ND Rule [] [Γ > Δ > [] |- [@ga _ (v2t ec) (take_lev (ec :: lev) ant2) (take_lev (ec :: lev) ant1) @@ lev] ].

      intros Γ Δ ec lev.
      refine (fix garrowfy ant1 ant2 (r:Arrange ant1 ant2):
           ND Rule [] [Γ > Δ > [] |- [@ga _ (v2t ec) (take_lev (ec :: lev) ant2) (take_lev (ec :: lev) ant1) @@ lev]] :=
        match r as R in Arrange A B return
          ND Rule [] [Γ > Δ > [] |- [@ga _ (v2t ec) (take_lev (ec :: lev) B) (take_lev (ec :: lev) A) @@ lev]]
          with
          | RCanL  a             => let case_RCanL := tt  in ga_uncancell _ _ _ _ _
          | RCanR  a             => let case_RCanR := tt  in ga_uncancelr _ _ _ _ _
          | RuCanL a             => let case_RuCanL := tt in ga_cancell _ _ _ _ _
          | RuCanR a             => let case_RuCanR := tt in ga_cancelr _ _ _ _ _
          | RAssoc a b c         => let case_RAssoc := tt in ga_assoc _ _ _ _ _ _ _
          | RCossa a b c         => let case_RCossa := tt in ga_unassoc _ _ _ _ _ _ _
          | RExch  a b           => let case_RExch := tt  in ga_swap  _ _ _ _ _ _
          | RWeak  a             => let case_RWeak := tt  in ga_drop  _ _ _ _ _ 
          | RCont  a             => let case_RCont := tt  in ga_copy  _ _ _ _ _ 
          | RLeft  a b c r'      => let case_RLeft := tt  in garrowfy _ _ r' ;; boost _ _ _ _ _ (ga_second _ _ _ _ _ _ _)
          | RRight a b c r'      => let case_RRight := tt in garrowfy _ _ r' ;; boost _ _ _ _ _ (ga_first  _ _ _ _ _ _ _)
          | RComp  a b c r1 r2   => let case_RComp := tt  in (fun r1' r2' => _) (garrowfy _ _ r1) (garrowfy _ _ r2)
        end); clear garrowfy; repeat take_simplify; repeat drop_simplify; intros.

        destruct case_RComp.
          refine ( _ ;; boost _ _ _ _ _ (ga_comp _ _ _ _ _ _ _)).
          apply seq.
          apply r2'.
          apply r1'.
          Defined.

  Definition garrowfy_arrangement :
    forall Γ (Δ:CoercionEnv Γ) n
      (ec:HaskTyVar Γ ★) (lev:HaskLevel Γ) (ant1 ant2:Tree ??(LeveledHaskType Γ ★)) (r:Arrange ant1 ant2) succ,
      ND Rule
      [Γ > Δ > mapOptionTree (garrowfy_leveled_code_types ((length lev))) (drop_depth n ant1)
        |- [@ga _ (v2t ec) (take_lev (ec :: lev) ant1) (mapOptionTree unlev succ) @@ lev]]
      [Γ > Δ > mapOptionTree (garrowfy_leveled_code_types ((length lev))) (drop_depth n ant2)
        |- [@ga _ (v2t ec) (take_lev (ec :: lev) ant2) (mapOptionTree unlev succ) @@ lev]].
      intros.
      refine ( _ ;; (boost _ _ _ _ _ (postcompose _ _ _ _ _ _ _ (garrowfy_arrangement' Γ Δ ec lev ant1 ant2 r)))).
      apply nd_rule.
      apply RArrange.
      refine ((fix garrowfy ant1 ant2 (r:Arrange ant1 ant2) :=
        match r as R in Arrange A B return
          Arrange (mapOptionTree (garrowfy_leveled_code_types ((length lev))) (drop_depth _ A))
          (mapOptionTree (garrowfy_leveled_code_types ((length lev))) (drop_depth _ B)) with
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
    forall n Γ Δ ant1 ant2 succ (r:Arrange ant1 ant2),
      ND Rule (mapOptionTree (flatten_judgment n) [Γ > Δ > ant1 |- succ])
      (mapOptionTree (flatten_judgment n) [Γ > Δ > ant2 |- succ]).
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

    set (Peano_dec.eq_nat_dec (Datatypes.length succ_lev) n) as lev_is_n.
      assert (lev_is_n=Peano_dec.eq_nat_dec (Datatypes.length succ_lev) n).
        reflexivity.
      destruct lev_is_n.
        rewrite <- e.
        apply garrowfy_arrangement.
        apply r.
        auto.
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
        Defined.

  Definition arrange_brak : forall Γ Δ ec succ t,
    ND Rule
     [Γ > Δ >
      mapOptionTree (garrowfy_leveled_code_types 0) (drop_depth (ec :: nil) succ),,
      [(@ga _ (v2t ec) [] (take_lev (ec :: nil) succ)) @@  nil] |- 
      [(@ga _ (v2t ec) [] [t]) @@  nil]]
        [Γ > Δ > mapOptionTree (garrowfy_leveled_code_types 0) succ |- [(@ga _ (v2t ec) [] [t]) @@  nil]].
    admit.
    Defined.

  Definition arrange_esc : forall Γ Δ ec succ t,
    ND Rule
     [Γ > Δ > mapOptionTree (garrowfy_leveled_code_types 0) succ |- [(@ga _ (v2t ec) [] [t]) @@  nil]]
     [Γ > Δ >
      mapOptionTree (garrowfy_leveled_code_types 0) (drop_depth (ec :: nil) succ),,
      [(@ga _ (v2t ec) [] (take_lev (ec :: nil) succ)) @@  nil] |- [(@ga _ (v2t ec) [] [t]) @@  nil]].
    admit.
    Defined.

  Lemma mapOptionTree_distributes
    : forall T R (a b:Tree ??T) (f:T->R),
      mapOptionTree f (a,,b) = (mapOptionTree f a),,(mapOptionTree f b).
    reflexivity.
    Qed.

  Lemma garrowfy_commutes_with_substT :
    forall n κ Γ (Δ:CoercionEnv Γ) (σ:∀ TV, InstantiatedTypeEnv TV Γ → TV κ → RawHaskType TV ★) (τ:HaskType Γ κ),
    garrowfy_code_types n (substT σ τ) = substT (fun TV ite v => garrowfy_raw_codetypes n (σ TV ite v))
      (garrowfy_code_types n τ).
    admit.
    Qed.

  Lemma garrowfy_commutes_with_HaskTAll :
    forall n κ Γ (Δ:CoercionEnv Γ) (σ:∀ TV, InstantiatedTypeEnv TV Γ → TV κ → RawHaskType TV ★),
    garrowfy_code_types n (HaskTAll κ σ) = HaskTAll κ (fun TV ite v => garrowfy_raw_codetypes n (σ TV ite v)).
    admit.
    Qed.

  Lemma garrowfy_commutes_with_HaskTApp :
    forall n κ Γ (Δ:CoercionEnv Γ) (σ:∀ TV, InstantiatedTypeEnv TV Γ → TV κ → RawHaskType TV ★),
    garrowfy_code_types n (HaskTApp (weakF σ) (FreshHaskTyVar κ)) =
    HaskTApp (weakF (fun TV ite v => garrowfy_raw_codetypes n (σ TV ite v))) (FreshHaskTyVar κ).
    admit.
    Qed.

  Lemma garrowfy_commutes_with_weakLT : forall (Γ:TypeEnv) κ n t,
    garrowfy_leveled_code_types n (weakLT(Γ:=Γ)(κ:=κ) t) = weakLT(Γ:=Γ)(κ:=κ) (garrowfy_leveled_code_types n t).
    admit.
    Qed.

  Definition flatten_proof :
    forall n {h}{c},
      ND Rule h c ->
      ND Rule (mapOptionTree (flatten_judgment n) h) (mapOptionTree (flatten_judgment n) c).
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
      apply (flatten_arrangement n Γ Δ a b x d).

    destruct case_RBrak.
      simpl.
      destruct (Peano_dec.eq_nat_dec (Datatypes.length lev) n).
      destruct lev.
      simpl.
      simpl.
      destruct n.
      change ([garrowfy_code_types 0 (<[ ec |- t ]>) @@  nil])
        with ([ga (v2t ec) [] [t] @@  nil]).
      refine (ga_unkappa Γ Δ (v2t ec) nil (take_lev (ec::nil) succ) [t]
        (mapOptionTree (garrowfy_leveled_code_types 0) (drop_depth (ec::nil) succ)) ;; _).
      apply arrange_brak.
      inversion e.
      apply (Prelude_error "found Brak at depth >0").
      apply (Prelude_error "found Brak at depth >0").

    destruct case_REsc.
      simpl.
      destruct (Peano_dec.eq_nat_dec (Datatypes.length lev) n).
      destruct lev.
      simpl.
      destruct n.
      change ([garrowfy_code_types 0 (<[ ec |- t ]>) @@  nil])
        with ([ga (v2t ec) [] [t] @@  nil]).
      refine (_ ;; ga_kappa Γ Δ (v2t ec) nil (take_lev (ec::nil) succ) [t]
        (mapOptionTree (garrowfy_leveled_code_types 0) (drop_depth (ec::nil) succ))).
      apply arrange_esc.
      inversion e.
      apply (Prelude_error "found Esc at depth >0").
      apply (Prelude_error "found Esc at depth >0").
      
    destruct case_RNote.
      simpl.
      destruct l; simpl.
        apply nd_rule; apply RNote; auto.
        destruct (Peano_dec.eq_nat_dec (Datatypes.length l) n).
        apply nd_rule; apply RNote; auto.
        apply nd_rule; apply RNote; auto.

    destruct case_RLit.
      simpl.
      destruct l0; simpl.
        rewrite literal_types_unchanged.
          apply nd_rule; apply RLit.
        destruct (Peano_dec.eq_nat_dec (Datatypes.length l0) n); unfold mapTree; unfold mapOptionTree; simpl.
        unfold take_lev; simpl.
        unfold drop_depth; simpl.
        apply ga_lit.
        rewrite literal_types_unchanged.
        apply nd_rule.
        apply RLit.

    destruct case_RVar.
      Opaque flatten_judgment.
      simpl.
      Transparent flatten_judgment.
      idtac.
      unfold flatten_judgment.
      unfold getjlev.
      destruct lev.
      apply nd_rule. apply RVar.
      destruct (eqd_dec (Datatypes.length lev) n).

      repeat drop_simplify.      
      repeat take_simplify.
      simpl.
      apply ga_id.      

      apply nd_rule.
      apply RVar.

    destruct case_RGlobal.
      simpl.
      destruct l as [|ec lev]; simpl; [ apply nd_rule; apply RGlobal; auto | idtac ].
      destruct (Peano_dec.eq_nat_dec (Datatypes.length lev) n); [ idtac | apply nd_rule; apply RGlobal; auto ]; simpl.
      apply (Prelude_error "found RGlobal at depth >0").

    destruct case_RLam.
      Opaque drop_depth.
      Opaque take_lev.
      simpl.
      destruct lev as [|ec lev]; simpl; [ apply nd_rule; apply RLam; auto | idtac ].
      destruct (Peano_dec.eq_nat_dec (Datatypes.length lev) n); [ idtac | apply nd_rule; apply RLam; auto ]; simpl.
      rewrite <- e.
      clear e n.
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
      destruct (Peano_dec.eq_nat_dec (Datatypes.length lev) n); [ idtac | apply nd_rule; apply RCast; auto ]; simpl.
      apply (Prelude_error "RCast at level >0").
      apply flatten_coercion; auto.

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
        replace (garrowfy_code_types n (tx ---> te)) with ((garrowfy_code_types n tx) ---> (garrowfy_code_types n te)).
        apply RApp.
        unfold garrowfy_code_types.
        simpl.
        reflexivity.

        destruct (Peano_dec.eq_nat_dec (Datatypes.length lev) n).
          eapply nd_comp.
          eapply nd_rule.
          apply RJoin.
          repeat drop_simplify.
          repeat take_simplify.
          apply boost.
          apply ga_apply.

          replace (garrowfy_code_types (minus' n (length (ec::lev))) (tx ---> te))
            with ((garrowfy_code_types (minus' n (length (ec::lev))) tx) --->
              (garrowfy_code_types (minus' n (length (ec::lev))) te)).
          apply nd_rule.
          apply RApp.
          unfold garrowfy_code_types.
          simpl.
          reflexivity.
(*
  Notation "`  x" := (take_lev _ x) (at level 20).
  Notation "`` x" := (mapOptionTree unlev x) (at level 20).
  Notation "``` x" := ((drop_depth _ x)) (at level 20).
  Notation "!<[]> x" := (garrowfy_code_types _ x) (at level 1).
  Notation "!<[@]>" := (garrowfy_leveled_code_types _) (at level 1).
*)
    destruct case_RLet.
      simpl.
      destruct lev as [|ec lev]; simpl; [ apply nd_rule; apply RLet; auto | idtac ].
      destruct (Peano_dec.eq_nat_dec (Datatypes.length lev) n); [ idtac | apply nd_rule; apply RLet; auto ]; simpl.
      repeat drop_simplify.
      repeat take_simplify.
      rename σ₁ into a.
      rename σ₂ into b.
      rewrite mapOptionTree_distributes.
      rewrite mapOptionTree_distributes.
      set (mapOptionTree (garrowfy_leveled_code_types (S n)) (drop_depth (ec :: lev) Σ₁)) as A.
      set (take_lev (ec :: lev) Σ₁) as A'.
      set (mapOptionTree (garrowfy_leveled_code_types (S n)) (drop_depth (ec :: lev) Σ₂)) as B.
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
      apply (Prelude_error "AppT at depth>0").

    destruct case_RAbsT.
      simpl. destruct lev; simpl.
      rewrite garrowfy_commutes_with_HaskTAll.
      rewrite garrowfy_commutes_with_HaskTApp.
      eapply nd_comp; [ idtac | eapply nd_rule; eapply RAbsT ].
      simpl.
      set (mapOptionTree (garrowfy_leveled_code_types n) (mapOptionTree (weakLT(κ:=κ)) Σ)) as a.
      set (mapOptionTree (weakLT(κ:=κ)) (mapOptionTree (garrowfy_leveled_code_types n) Σ)) as q'.
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
