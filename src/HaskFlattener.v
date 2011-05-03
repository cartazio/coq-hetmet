(*********************************************************************************************************************************)
(* HaskFlattener:                                                                                                           *)
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

  (* In a tree of types, replace any type at level "lev" with None *)
  Definition drop_lev {Γ}(lev:HaskLevel Γ)(tt:Tree ??(LeveledHaskType Γ ★)) : Tree ??(LeveledHaskType Γ ★) :=
    mapTree (fun t => match t with
                        | Some (ttype @@ tlev) => if eqd_dec tlev lev then None else t
                        | _ => t
                      end) tt.
  (* The opposite: replace any type which is NOT at level "lev" with None *)
  Definition take_lev {Γ}(lev:HaskLevel Γ)(tt:Tree ??(LeveledHaskType Γ ★)) : Tree ??(HaskType Γ ★) :=
    mapTree (fun t => match t with
                        | Some (ttype @@ tlev) => if eqd_dec tlev lev then Some ttype else None
                        | _                    => None
                      end) tt.

  (* In a tree of types, replace any type at depth "lev" or greater None *)
  Definition drop_depth {Γ}(n:nat)(tt:Tree ??(LeveledHaskType Γ ★)) : Tree ??(LeveledHaskType Γ ★) :=
    mapTree (fun t => match t with
                        | Some (ttype @@ tlev) => if eqd_dec (length tlev) n then None else t
                        | _ => t
                      end) tt.

  (* delete from the tree any type which is NOT at level "lev" *)

  Fixpoint take_lev' {Γ}(lev:HaskLevel Γ)(tt:Tree ??(LeveledHaskType Γ ★)) : ??(Tree ??(HaskType Γ ★)) :=
    match tt with
      | T_Leaf   None  => Some (T_Leaf None)    (* FIXME: unsure of this; it ends up on both sides *)
      | T_Branch b1 b2 =>
        let b1' := take_lev' lev b1 in
          let b2' := take_lev' lev b2 in
            match b1' with
              | None => b2'
              | Some b1'' => match b2' with
                               | None => Some b1''
                               | Some b2'' => Some (b1'',,b2'')
                             end
            end
      | T_Leaf   (Some (ttype@@tlev))  =>
                if eqd_dec tlev lev
                  then Some [ttype]
                  else None
    end.

  Context (ga' : forall TV, TV ★ -> Tree ??(RawHaskType TV ★) -> Tree ??(RawHaskType TV ★) -> RawHaskType TV ★).

  Definition ga : forall Γ, HaskTyVar Γ ★ -> Tree ??(HaskType Γ ★) -> Tree ??(HaskType Γ ★) -> HaskType Γ ★
    := fun Γ ec ant suc =>
      fun TV ite =>
        ga'
        TV
        (ec TV ite)
        (mapOptionTree (fun x => x TV ite) ant)
        (mapOptionTree (fun x => x TV ite) suc).

  Implicit Arguments ga [ [Γ] ].
  Notation "a ~~~~> b" := (@ga _ _ a b) (at level 20).

  Context (unit_type : forall TV, RawHaskType TV ★).

  (*
   *  The story:
   *    - code types <[t]>@c                                                become garrows  c () t 
   *    - free variables of type t at a level lev deeper than the succedent become garrows  c () t
   *    - free variables at the level of the succedent become 
   *)
  Fixpoint flatten_rawtype {TV}{κ}(depth:nat)(exp: RawHaskType TV κ) : RawHaskType TV κ :=
    match exp with
    | TVar    _  x        => TVar x
    | TAll     _ y        => TAll   _  (fun v => flatten_rawtype depth (y v))
    | TApp   _ _ x y      => TApp      (flatten_rawtype depth x) (flatten_rawtype depth y)
    | TCon       tc       => TCon      tc
    | TCoerc _ t1 t2 t    => TCoerc    (flatten_rawtype depth t1) (flatten_rawtype depth t2) (flatten_rawtype depth t)
    | TArrow              => TArrow
    | TCode      v e      => match depth with
                               | O => match v return RawHaskType TV ★ with
                                        | TVar ★ ec => ga' TV ec [] [flatten_rawtype depth e]
                                        | _         => unit_type TV
                                      end
                               | (S depth') => TCode v (flatten_rawtype depth' e)
                             end
    | TyFunApp     tfc lt => TyFunApp tfc (flatten_rawtype_list _ depth lt)
    end
    with flatten_rawtype_list {TV}(lk:list Kind)(depth:nat)(exp:@RawHaskTypeList TV lk) : @RawHaskTypeList TV lk :=
    match exp in @RawHaskTypeList _ LK return @RawHaskTypeList TV LK with
    | TyFunApp_nil               => TyFunApp_nil
    | TyFunApp_cons  κ kl t rest => TyFunApp_cons _ _ (flatten_rawtype depth t) (flatten_rawtype_list _ depth rest)
    end.

  Inductive AllT {T:Type}{P:T->Prop} : Tree ??T -> Prop :=
    | allt_none   :                  AllT []
    | allt_some   : forall t, P t -> AllT [t]
    | allt_branch : forall b1 b2, AllT b1 -> AllT b2 -> AllT (b1,,b2)
    .
  Implicit Arguments AllT [[T]].

  Definition getΓ (j:Judg) := match j with Γ > _ > _ |- _ => Γ end.

  Definition getSuc (j:Judg) : Tree ??(LeveledHaskType (getΓ j) ★) :=
    match j as J return Tree ??(LeveledHaskType (getΓ J) ★) with
      Γ > _ > _ |- s => s
        end.

  Definition getlev {Γ}{κ}(lht:LeveledHaskType Γ κ) :=
    match lht with t@@l => l end.

  (* This tries to assign a single level to the entire succedent of a judgment.  If the succedent has types from different
   * levels (should not happen) it just picks one; if the succedent has no non-None leaves (also should not happen) it
   * picks nil *)
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

  (* an XJudg is a Judg for which the SUCCEDENT types all come from the same level, and that level is no deeper than "n" *)
  (* even the empty succedent [] has a level... *)
  Definition QJudg (n:nat)(j:Judg) := le (length (getjlev (getSuc j))) n.

(*  Definition qjudg2judg {n}(qj:QJudg n) : Judg := projT1 qj.*)

  Inductive QRule : nat -> Tree ??Judg -> Tree ??Judg -> Type :=
    mkQRule : forall n h c,
      Rule h c ->
      ITree _ (QJudg n) h ->
      ITree _ (QJudg n) c ->
      QRule n h c.

  Definition QND n := ND (QRule n).

  (*
   * Any type   "t"   at a level with length "n"   becomes (g () t)
   * Any type "<[t]>" at a level with length "n-1" becomes (g () t)
   *)

  Definition flatten_type {Γ}(n:nat)(ht:HaskType Γ ★) : HaskType Γ ★ :=
    fun TV ite =>
      flatten_rawtype n (ht TV ite).

  Definition minus' n m :=
    match m with
      | 0 => n
      | _ => n - m
    end.

  (* to do: integrate this more cleanly with qjudg *)
  Definition flatten_leveled_type {Γ}(n:nat)(ht:LeveledHaskType Γ ★) : LeveledHaskType Γ ★ :=
    match ht with
      htt @@ htlev =>
      flatten_type (minus' n (length htlev)) htt @@ htlev
    end.

  Definition flatten_qjudg_ok (n:nat)(j:Judg) : Judg :=
    match j with
      Γ > Δ > ant |- suc =>
        let ant' := mapOptionTree (flatten_leveled_type n) ant in
          let suc' := mapOptionTree (flatten_leveled_type n) suc
            in  (Γ > Δ > ant' |- suc')
    end.

  Definition take_lev'' {Γ}(lev:HaskLevel Γ)(tt:Tree ??(LeveledHaskType Γ ★)) : Tree ??(HaskType Γ ★) :=
    match (take_lev' lev tt) with
      | None => []
      | Some x => x
    end.

  Definition flatten_qjudg : forall (n:nat), Judg -> Judg.
    refine (fun {n}{j} =>
      match j as J return Judg with
        Γ > Δ > ant |- suc =>
          match getjlev suc with
            | nil        => flatten_qjudg_ok n j
            | (ec::lev') => if eqd_dec (length lev') n
                            then let ant_host    := drop_depth (S n) ant in
                                   let ant_guest := take_lev (ec::lev') ant in  (* FIXME: I want take_lev''!!!!! *)
                                     (Γ > Δ > ant_host |- [ga ec ant_guest (mapOptionTree unlev suc) @@ lev'])
                            else flatten_qjudg_ok n j
          end
      end).
    Defined.

  Axiom literal_types_unchanged : forall n Γ l, flatten_type n (literalType l) = literalType(Γ:=Γ) l.

  Lemma drop_depth_lemma : forall Γ (lev:HaskLevel Γ) x, drop_depth (length lev) [x @@  lev] = [].
    admit.
    Defined.

  Lemma drop_depth_lemma_s : forall Γ (lev:HaskLevel Γ) ec x, drop_depth (S (length lev)) [x @@  (ec :: lev)] = [].
    admit.
    Defined.

  Ltac drop_simplify :=
    match goal with
      | [ |- context[@drop_depth ?G (length ?L) [ ?X @@ ?L ] ] ] =>
        rewrite (drop_depth_lemma G L X)
      | [ |- context[@drop_depth ?G (S (length ?L)) [ ?X @@ (?E :: ?L) ] ] ] =>
        rewrite (drop_depth_lemma_s G L E X)
      | [ |- context[@drop_depth ?G ?N (?A,,?B)] ] =>
      change (@drop_depth G N (A,,B)) with ((@drop_depth G N A),,(@drop_depth G N B))
      | [ |- context[@drop_depth ?G ?N (T_Leaf None)] ] =>
      change (@drop_depth G N (T_Leaf (@None (LeveledHaskType G ★)))) with (T_Leaf (@None (LeveledHaskType G ★)))
    end.

  Lemma take_lemma : forall Γ (lev:HaskLevel Γ) x, take_lev lev [x @@  lev] = [x].
    admit.
    Defined.

  Ltac take_simplify :=
    match goal with
      | [ |- context[@take_lev ?G ?L [ ?X @@ ?L ] ] ] =>
        rewrite (take_lemma G L X)
      | [ |- context[@take_lev ?G ?N (?A,,?B)] ] =>
      change (@take_lev G N (A,,B)) with ((@take_lev G N A),,(@take_lev G N B))
      | [ |- context[@take_lev ?G ?N (T_Leaf None)] ] =>
      change (@take_lev G N (T_Leaf (@None (LeveledHaskType G ★)))) with (T_Leaf (@None (LeveledHaskType G ★)))
    end.

  Class garrow :=
  { ga_id        : ∀ Γ Δ ec lev a    , ND Rule [] [Γ > Δ >                                           [] |- [@ga Γ ec a a @@ lev] ]
  ; ga_comp      : ∀ Γ Δ ec lev a b c, ND Rule [] [Γ > Δ > [@ga Γ ec a b @@ lev],,[@ga Γ ec b c @@ lev] |- [@ga Γ ec a c @@ lev] ] 
  ; ga_cancelr   : ∀ Γ Δ ec lev a    , ND Rule [] [Γ > Δ >                                           [] |- [@ga Γ ec (a,,[]) a @@ lev] ]
  ; ga_cancell   : ∀ Γ Δ ec lev a    , ND Rule [] [Γ > Δ >                                           [] |- [@ga Γ ec ([],,a) a @@ lev] ]
  ; ga_uncancelr : ∀ Γ Δ ec lev a    , ND Rule [] [Γ > Δ >                                           [] |- [@ga Γ ec a (a,,[]) @@ lev] ]
  ; ga_uncancell : ∀ Γ Δ ec lev a    , ND Rule [] [Γ > Δ >                                           [] |- [@ga Γ ec a ([],,a) @@ lev] ]
  ; ga_assoc     : ∀ Γ Δ ec lev a b c, ND Rule [] [Γ > Δ >                                           [] |- [@ga Γ ec ((a,,b),,c) (a,,(b,,c)) @@ lev] ]
  ; ga_unassoc   : ∀ Γ Δ ec lev a b c, ND Rule [] [Γ > Δ >                                           [] |- [@ga Γ ec (a,,(b,,c)) ((a,,b),,c) @@ lev] ]
  ; ga_swap      : ∀ Γ Δ ec lev a b  , ND Rule [] [Γ > Δ >                                           [] |- [@ga Γ ec (a,,b) (b,,a) @@ lev] ]
  ; ga_drop      : ∀ Γ Δ ec lev a    , ND Rule [] [Γ > Δ >                                           [] |- [@ga Γ ec a [] @@ lev] ]
  ; ga_copy      : ∀ Γ Δ ec lev a    , ND Rule [] [Γ > Δ >                                           [] |- [@ga Γ ec a (a,,a) @@ lev] ]
  ; ga_first     : ∀ Γ Δ ec lev a b x, ND Rule [] [Γ > Δ >                        [@ga Γ ec a b @@ lev] |- [@ga Γ ec (a,,x) (b,,x) @@ lev] ]
  ; ga_second    : ∀ Γ Δ ec lev a b x, ND Rule [] [Γ > Δ >                        [@ga Γ ec a b @@ lev] |- [@ga Γ ec (x,,a) (x,,b) @@ lev] ]
  ; ga_lit       : ∀ Γ Δ ec lev lit  , ND Rule [] [Γ > Δ >                                           [] |- [@ga Γ ec [] [literalType lit] @@ lev] ]
  ; ga_curry     : ∀ Γ Δ ec lev a b c, ND Rule [] [Γ > Δ >               [@ga Γ ec (a,,[b]) [c] @@ lev] |- [@ga Γ ec a [b ---> c] @@ lev] ]
  ; ga_apply     : ∀ Γ Δ ec lev a a' b c, ND Rule [] [Γ > Δ >
    [@ga Γ ec a [b ---> c] @@ lev],,[@ga Γ ec a' [b] @@ lev]
    |-
    [@ga Γ ec (a,,a') [c] @@ lev] ]
  }.

  Context (gar:garrow).

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
  Definition precompose : ∀ Γ Δ lev a b c x,
     ND Rule [] [ Γ > Δ > a |- x,,[b @@ lev] ] ->
     ND Rule [] [ Γ > Δ > [b @@ lev] |- [c @@ lev] ] ->
     ND Rule [] [ Γ > Δ > a,,x |- [c @@ lev] ].
     admit.
     Defined.

  Set Printing Width 130.

  Definition garrowfy_arrangement' :
    forall Γ (Δ:CoercionEnv Γ)
      (ec:HaskTyVar Γ ★) (lev:HaskLevel Γ) (ant1 ant2:Tree ??(LeveledHaskType Γ ★)) (r:Arrange ant1 ant2),
      ND Rule [] [Γ > Δ > [] |- [@ga _ ec (take_lev (ec :: lev) ant2) (take_lev (ec :: lev) ant1) @@ lev] ].

      intros Γ Δ ec lev.
      refine (fix garrowfy ant1 ant2 (r:Arrange ant1 ant2):
           ND Rule [] [Γ > Δ > [] |- [@ga _ ec (take_lev (ec :: lev) ant2) (take_lev (ec :: lev) ant1) @@ lev]] :=
        match r as R in Arrange A B return
          ND Rule [] [Γ > Δ > [] |- [@ga _ ec (take_lev (ec :: lev) B) (take_lev (ec :: lev) A) @@ lev]]
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
          (*
          set (ga_comp Γ Δ ec lev (``c) (``b) (``a)) as q.
          eapply precompose.
          Focus 2.
          apply q.
          refine ( _ ;; boost _ _ _ _ _ (ga_comp _ _ _ _ _ _ _)).
          apply precompose.
          Focus 2.
          eapply ga_comp.
          *)
          admit.
          Defined.

  Definition garrowfy_arrangement :
    forall Γ (Δ:CoercionEnv Γ) n
      (ec:HaskTyVar Γ ★) (lev:HaskLevel Γ) (ant1 ant2:Tree ??(LeveledHaskType Γ ★)) (r:Arrange ant1 ant2) succ,
      (*ec :: lev = getjlev succ ->*)
      (* H0 : left (Datatypes.length lev ≠ n) e = Peano_dec.eq_nat_dec (Datatypes.length lev) n *)
      ND Rule
      [Γ > Δ > drop_depth n ant1 |- [@ga _ ec (take_lev (ec :: lev) ant1) (mapOptionTree unlev succ) @@ lev]]
      [Γ > Δ > drop_depth n ant2 |- [@ga _ ec (take_lev (ec :: lev) ant2) (mapOptionTree unlev succ) @@ lev]].
      intros.
      refine ( _ ;; (boost _ _ _ _ _ (postcompose _ _ _ _ _ _ _ (garrowfy_arrangement' Γ Δ ec lev ant1 ant2 r)))).
      apply nd_rule.
      apply RArrange.
      refine ((fix garrowfy ant1 ant2 (r:Arrange ant1 ant2) :=
        match r as R in Arrange A B return Arrange (drop_depth _ A) (drop_depth _ B) with
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
      ND Rule (mapOptionTree (flatten_qjudg n) [Γ > Δ > ant1 |- succ])
      (mapOptionTree (flatten_qjudg n) [Γ > Δ > ant2 |- succ]).
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

  Lemma flatten_coercion : forall n Γ Δ σ τ (γ:HaskCoercion Γ Δ (σ ∼∼∼ τ)),
    HaskCoercion Γ Δ (flatten_type n σ ∼∼∼ flatten_type n τ).
    admit.
    Defined.

  Ltac eqd_dec_refl' :=
    match goal with
      | [ |- context[@eqd_dec ?T ?V ?X ?X] ] =>
        destruct (@eqd_dec T V X X) as [eqd_dec1 | eqd_dec2];
          [ clear eqd_dec1 | set (eqd_dec2 (refl_equal _)) as eqd_dec2'; inversion eqd_dec2' ]
  end.


(*
  Lemma foog : forall Γ Δ,
    ND Rule
    ( [ Γ > Δ > Σ₁ |- a ],,[ Γ > Δ > Σ₂ |- b ] )
      [ Γ > Δ > Σ₁,,Σ₂ |- a,,b ]
*)

  Notation "`  x" := (take_lev _ x) (at level 20).
  Notation "`` x" := (mapOptionTree unlev x) (at level 20).
  Notation "``` x" := (drop_depth _ x) (at level 20).

  Definition flatten :
    forall n {h}{c},
      QND (S n) h c ->
      ND Rule (mapOptionTree (flatten_qjudg n) h) (mapOptionTree (flatten_qjudg n) c).
    intros.
    eapply nd_map'; [ idtac | apply X ].
    clear h c X.
    intros.
    simpl in *.

    inversion X.
    subst.
    refine (match X0 as R in Rule H C with
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
      | RBrak    Σ a b c n m           => let case_RBrak := tt         in _
      | REsc     Σ a b c n m           => let case_REsc := tt          in _
      | RCase    Γ Δ lev tc Σ avars tbranches alts => let case_RCase := tt         in _
      | RLetRec  Γ Δ lri x y t         => let case_RLetRec := tt       in _
      end); clear X X0 X1 X2 h c.

    destruct case_RArrange.
      apply (flatten_arrangement n Γ Δ a b x d).

    destruct case_RBrak.
      admit.

    destruct case_REsc.
      admit.
      
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
      simpl.
      destruct lev as [|ec lev]; simpl; [ apply nd_rule; apply RVar | idtac ].
      destruct (Peano_dec.eq_nat_dec (Datatypes.length lev) n); [ idtac | apply nd_rule; apply RVar ]; simpl.
      rewrite <- e.
      clear e n.
      repeat drop_simplify.
      repeat take_simplify.
      apply ga_id.

    destruct case_RGlobal.
      simpl.
      destruct l as [|ec lev]; simpl; [ apply nd_rule; apply RGlobal; auto | idtac ].
      destruct (Peano_dec.eq_nat_dec (Datatypes.length lev) n); [ idtac | apply nd_rule; apply RGlobal; auto ]; simpl.
      apply (Prelude_error "found RGlobal at depth >0").

    destruct case_RLam.
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
        replace (flatten_type n (tx ---> te)) with ((flatten_type n tx) ---> (flatten_type n te)).
        apply RApp.
        unfold flatten_type.
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

          replace (flatten_type (minus' n (length (ec::lev))) (tx ---> te))
            with ((flatten_type (minus' n (length (ec::lev))) tx) ---> (flatten_type (minus' n (length (ec::lev))) te)).
          apply nd_rule.
          apply RApp.
          unfold flatten_type.
          simpl.
          reflexivity.

    destruct case_RLet.
      simpl.
      destruct lev as [|ec lev]; simpl; [ apply nd_rule; apply RLet; auto | idtac ].
      destruct (Peano_dec.eq_nat_dec (Datatypes.length lev) n); [ idtac | apply nd_rule; apply RLet; auto ]; simpl.
      repeat drop_simplify.
      repeat take_simplify.
      admit.  (* FIXME *)

    destruct case_RVoid.
      simpl.
      apply nd_rule.
      apply RVoid.
        
    destruct case_RAppT.
      simpl. destruct lev; simpl.
      admit.
      admit.

    destruct case_RAbsT.
      simpl. destruct lev; simpl.
      admit.
      admit.

    destruct case_RAppCo.
      simpl. destruct lev; simpl.
      admit.
      admit.

    destruct case_RAbsCo.
      simpl. destruct lev; simpl.
      admit.
      admit.

    destruct case_RLetRec.
      simpl.
      admit.

    destruct case_RCase.
      simpl.
      admit.
      Defined.

    Lemma flatten_qjudg_qjudg : forall {n}{j} (q:QJudg (S n) j), QJudg n (flatten_qjudg n j).
      admit.
      (*
      intros.
      destruct q.
      destruct a.
      unfold flatten_qjudg.
      destruct j.
      destruct (eqd_dec (Datatypes.length x) (S n)).
      destruct x.
      inversion e.
      exists x; split.
        simpl in e.
        inversion e.
        auto.
        simpl in *.
        apply allt_some.
        simpl.
        auto.
      unfold QJudg.
      exists x.
      split; auto.
        clear a.
        Set Printing Implicit.
        simpl.
        set (length x) as x'.
        assert (x'=length x).
          reflexivity.
          simpl in *.
          rewrite <- H.
          Unset Printing Implicit.
          idtac.
          omega.
    simpl in *.
      induction t0.
      destruct a0; simpl in *.
      apply allt_some.
      inversion a.
      subst.
      destruct l0.
      simpl.
      auto.
      apply allt_none.
      simpl in *.
      inversion a; subst.
      apply allt_branch.
        apply IHt0_1; auto.
        apply IHt0_2; auto.
        *)
        Defined.


  (*
  Instance FlatteningFunctor {Γ}{Δ}{ec} : Functor (JudgmentsL (PCF Γ Δ ec)) (TypesL (SystemFCa Γ Δ)) (obact) :=
    { fmor := FlatteningFunctor_fmor }.
    Admitted.

  Definition ReificationFunctor Γ Δ : Functor (JudgmentsL _ _ (PCF n Γ Δ)) SystemFCa' (mapOptionTree brakifyJudg).
    refine {| fmor := ReificationFunctor_fmor Γ Δ |}; unfold hom; unfold ob; simpl ; intros.
    Admitted.

  Definition PCF_SMME (n:nat)(Γ:TypeEnv)(Δ:CoercionEnv Γ) : ProgrammingLanguageSMME.
    refine {| plsmme_pl := PCF n Γ Δ |}.
    admit.
    Defined.

  Definition SystemFCa_SMME (n:nat)(Γ:TypeEnv)(Δ:CoercionEnv Γ) : ProgrammingLanguageSMME.
    refine {| plsmme_pl := SystemFCa n Γ Δ |}.
    admit.
    Defined.

  Definition ReificationFunctorMonoidal n : MonoidalFunctor (JudgmentsN n) (JudgmentsN (S n)) (ReificationFunctor n).
    admit.
    Defined.

  (* 5.1.4 *)
  Definition PCF_SystemFCa_two_level n Γ Δ : TwoLevelLanguage (PCF_SMME n Γ Δ) (SystemFCa_SMME (S n) Γ Δ).
    admit.
    Defined.
  *)
  (*  ... and the retraction exists *)

End HaskFlattener.









(*

  Old flattening code; ignore this - just to remind me how I used to do it

  (*
   * Here it is, what you've all been waiting for!  When reading this,
   * it might help to have the definition for "Inductive ND" (see
   * NaturalDeduction.v) handy as a cross-reference.
   *)
  Hint Constructors Rule_Flat.
  Definition FlatteningFunctor_fmor
    : forall h c,
      (ND (PCFRule Γ Δ ec) h c) ->
      ((obact h)====>(obact c)).

    set (@nil (HaskTyVar Γ ★)) as lev.

    unfold hom; unfold ob; unfold ehom; simpl; unfold pmon_I; unfold obact; intros.

    induction X; simpl.

    (* the proof from no hypotheses of no conclusions (nd_id0) becomes RVoid *)
    apply nd_rule; apply (org_fc Γ Δ [] [(_,_)] (RVoid _ _)). apply Flat_RVoid.

    (* the proof from hypothesis X of conclusion X (nd_id1) becomes RVar *)
    apply nd_rule; apply (org_fc _ _ [] [(_,_)] (RVar _ _ _ _)). apply Flat_RVar.

    (* the proof from hypothesis X of no conclusions (nd_weak) becomes RWeak;;RVoid *)
    eapply nd_comp;
      [ idtac
      | eapply nd_rule
      ; eapply (org_fc  _ _ [(_,_)] [(_,_)] (RArrange _ _ _ _ _ (RWeak _)))
      ; auto ].
      eapply nd_rule.
      eapply (org_fc _ _ [] [(_,_)] (RVoid _ _)); auto. apply Flat_RVoid.
      apply Flat_RArrange.

    (* the proof from hypothesis X of two identical conclusions X,,X (nd_copy) becomes RVar;;RJoin;;RCont *)
    eapply nd_comp; [ idtac | eapply nd_rule; eapply (org_fc _ _ [(_,_)] [(_,_)] (RArrange _ _ _ _ _ (RCont _))) ].
      eapply nd_comp; [ apply nd_llecnac | idtac ].
      set (snd_initial(SequentND:=pl_snd(ProgrammingLanguage:=SystemFCa Γ Δ))
        (mapOptionTree (guestJudgmentAsGArrowType) h @@@ lev)) as q.
      eapply nd_comp.
      eapply nd_prod.
      apply q.
      apply q.
      apply nd_rule. 
      eapply (org_fc _ _ ([(_,_)],,[(_,_)]) [(_,_)] (RJoin _ _ _ _ _ _ )).
      destruct h; simpl.
      destruct o.
      simpl.
      apply Flat_RJoin.
      apply Flat_RJoin.
      apply Flat_RJoin.
      apply Flat_RArrange.

    (* nd_prod becomes nd_llecnac;;nd_prod;;RJoin *)
    eapply nd_comp.
      apply (nd_llecnac ;; nd_prod IHX1 IHX2).
      apply nd_rule.
      eapply (org_fc _ _ ([(_,_)],,[(_,_)]) [(_,_)] (RJoin _ _ _ _ _ _ )).
      apply (Flat_RJoin Γ Δ (mapOptionTree guestJudgmentAsGArrowType h1 @@@ nil)
       (mapOptionTree guestJudgmentAsGArrowType h2 @@@ nil)
       (mapOptionTree guestJudgmentAsGArrowType c1 @@@ nil)
       (mapOptionTree guestJudgmentAsGArrowType c2 @@@ nil)).

    (* nd_comp becomes pl_subst (aka nd_cut) *)
    eapply nd_comp.
      apply (nd_llecnac ;; nd_prod IHX1 IHX2).
      clear IHX1 IHX2 X1 X2.
      apply (@snd_cut _ _ _ _ (pl_snd(ProgrammingLanguage:=SystemFCa Γ Δ))). 

    (* nd_cancell becomes RVar;;RuCanL *)
    eapply nd_comp;
      [ idtac | eapply nd_rule; apply (org_fc _ _ [(_,_)] [(_,_)] (RArrange _ _ _ _ _ (RuCanL _))) ].
      apply (snd_initial(SequentND:=pl_cnd(ProgrammingLanguage:=(SystemFCa Γ Δ)))).
      apply Flat_RArrange.

    (* nd_cancelr becomes RVar;;RuCanR *)
    eapply nd_comp;
      [ idtac | eapply nd_rule; apply (org_fc _ _ [(_,_)] [(_,_)] (RArrange _ _ _ _ _ (RuCanR _))) ].
      apply (snd_initial(SequentND:=pl_cnd(ProgrammingLanguage:=(SystemFCa Γ Δ)))).
      apply Flat_RArrange.

    (* nd_llecnac becomes RVar;;RCanL *)
    eapply nd_comp;
      [ idtac | eapply nd_rule; apply (org_fc _ _ [(_,_)] [(_,_)] (RArrange _ _ _ _ _ (RCanL _))) ].
      apply (snd_initial(SequentND:=pl_cnd(ProgrammingLanguage:=(SystemFCa Γ Δ)))).
      apply Flat_RArrange.

    (* nd_rlecnac becomes RVar;;RCanR *)
    eapply nd_comp;
      [ idtac | eapply nd_rule; apply (org_fc _ _ [(_,_)] [(_,_)] (RArrange _ _ _ _ _ (RCanR _))) ].
      apply (snd_initial(SequentND:=pl_cnd(ProgrammingLanguage:=(SystemFCa Γ Δ)))).
      apply Flat_RArrange.

    (* nd_assoc becomes RVar;;RAssoc *)
    eapply nd_comp;
      [ idtac | eapply nd_rule; apply (org_fc _ _ [(_,_)] [(_,_)] (RArrange _ _ _ _ _ (RAssoc _ _ _))) ].
      apply (snd_initial(SequentND:=pl_cnd(ProgrammingLanguage:=(SystemFCa Γ Δ)))).
      apply Flat_RArrange.

    (* nd_cossa becomes RVar;;RCossa *)
    eapply nd_comp;
      [ idtac | eapply nd_rule; apply (org_fc _ _ [(_,_)] [(_,_)] (RArrange _ _ _ _ _ (RCossa _ _ _))) ].
      apply (snd_initial(SequentND:=pl_cnd(ProgrammingLanguage:=(SystemFCa Γ Δ)))).
      apply Flat_RArrange.

      destruct r as [r rp].
      rename h into h'.
      rename c into c'.
      rename r into r'.

      refine (match rp as R in @Rule_PCF _ _ _ H C _
                return
                ND (OrgR Γ Δ) []
                [sequent (mapOptionTree guestJudgmentAsGArrowType H @@@ nil)
                  (mapOptionTree guestJudgmentAsGArrowType C @@@ nil)]
                with
                | PCF_RArrange         h c r q          => let case_RURule        := tt in _
                | PCF_RLit             lit              => let case_RLit          := tt in _
                | PCF_RNote            Σ τ   n          => let case_RNote         := tt in _
                | PCF_RVar             σ                => let case_RVar          := tt in _
                | PCF_RLam             Σ tx te          => let case_RLam          := tt in _
                | PCF_RApp             Σ tx te   p      => let case_RApp          := tt in _
                | PCF_RLet             Σ σ₁ σ₂   p      => let case_RLet          := tt in _
                | PCF_RJoin    b c d e          => let case_RJoin := tt in _
                | PCF_RVoid                       => let case_RVoid   := tt in _
              (*| PCF_RCase            T κlen κ θ l x   => let case_RCase         := tt in _*)
              (*| PCF_RLetRec          Σ₁ τ₁ τ₂ lev     => let case_RLetRec       := tt in _*)
              end); simpl in *.
      clear rp h' c' r'.

      rewrite (unlev_lemma h (ec::nil)).
      rewrite (unlev_lemma c (ec::nil)).
      destruct case_RURule.
        refine (match q as Q in Arrange H C
                return
                H=(h @@@ (ec :: nil)) ->
                C=(c @@@ (ec :: nil)) ->
                ND (OrgR Γ Δ) []
                [sequent
                  [ga_type (ga_rep (mapOptionTree unlev H)) (ga_rep r) @@ nil ]
                  [ga_type (ga_rep (mapOptionTree unlev C)) (ga_rep r) @@ nil ] ]
                  with
          | RLeft   a b c r => let case_RLeft  := tt in _
          | RRight  a b c r => let case_RRight := tt in _
          | RCanL     b     => let case_RCanL  := tt in _
          | RCanR     b     => let case_RCanR  := tt in _
          | RuCanL    b     => let case_RuCanL := tt in _
          | RuCanR    b     => let case_RuCanR := tt in _
          | RAssoc    b c d => let case_RAssoc := tt in _
          | RCossa    b c d => let case_RCossa := tt in _
          | RExch     b c   => let case_RExch  := tt in _
          | RWeak     b     => let case_RWeak  := tt in _
          | RCont     b     => let case_RCont  := tt in _
          | RComp a b c f g => let case_RComp  := tt in _
        end (refl_equal _) (refl_equal _));
        intros; simpl in *;
        subst;
        try rewrite <- unlev_lemma in *.

      destruct case_RCanL.
        apply magic.
        apply ga_uncancell.
        
      destruct case_RCanR.
        apply magic.
        apply ga_uncancelr.

      destruct case_RuCanL.
        apply magic.
        apply ga_cancell.

      destruct case_RuCanR.
        apply magic.
        apply ga_cancelr.

      destruct case_RAssoc.
        apply magic.
        apply ga_assoc.
        
      destruct case_RCossa.
        apply magic.
        apply ga_unassoc.

      destruct case_RExch.
        apply magic.
        apply ga_swap.
        
      destruct case_RWeak.
        apply magic.
        apply ga_drop.
        
      destruct case_RCont.
        apply magic.
        apply ga_copy.
        
      destruct case_RLeft.
        apply magic.
        (*apply ga_second.*)
        admit.
        
      destruct case_RRight.
        apply magic.
        (*apply ga_first.*)
        admit.

      destruct case_RComp.
        apply magic.
        (*apply ga_comp.*)
        admit.

      destruct case_RLit.
        apply ga_lit.

      (* hey cool, I figured out how to pass CoreNote's through... *)
      destruct case_RNote.
        eapply nd_comp.
        eapply nd_rule.
        eapply (org_fc _ _ [] [(_,_)] (RVar _ _ _ _)) . auto.
        apply Flat_RVar.
        apply nd_rule.
        apply (org_fc _ _ [(_,_)] [(_,_)] (RNote _ _ _ _ _ n)). auto.
        apply Flat_RNote.
        
      destruct case_RVar.
        apply ga_id.

      (*
       *   class GArrow g (**) u => GArrowApply g (**) u (~>) where
       *     ga_applyl    :: g (x**(x~>y)   ) y
       *     ga_applyr    :: g (   (x~>y)**x) y
       *   
       *   class GArrow g (**) u => GArrowCurry g (**) u (~>) where
       *     ga_curryl    :: g (x**y) z  ->  g x (y~>z)
       *     ga_curryr    :: g (x**y) z  ->  g y (x~>z)
       *)
      destruct case_RLam.
        (* GArrowCurry.ga_curry *)
        admit.

      destruct case_RApp.
        (* GArrowApply.ga_apply *)
        admit.

      destruct case_RLet.
        admit.

      destruct case_RVoid.
        apply ga_id.

      destruct case_RJoin.
        (* this assumes we want effects to occur in syntactically-left-to-right order *)
        admit.
        Defined.
*)