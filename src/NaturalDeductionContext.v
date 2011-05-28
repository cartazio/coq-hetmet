(*********************************************************************************************************************************)
(* NaturalDeductionContext:                                                                                                      *)
(*                                                                                                                               *)
(*   Manipulations of a context in natural deduction proofs.                                                                     *)
(*                                                                                                                               *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import NaturalDeduction.

Section NaturalDeductionContext.

  (* Figure 3, production $\vdash_E$, Uniform rules *)
  Inductive Arrange {T} : Tree ??T -> Tree ??T -> Type :=
  | RId     : forall a        ,                Arrange           a                  a
  | RCanL   : forall a        ,                Arrange  (    [],,a   )      (       a   )
  | RCanR   : forall a        ,                Arrange  (    a,,[]   )      (       a   )
  | RuCanL  : forall a        ,                Arrange  (       a    )      (  [],,a    )
  | RuCanR  : forall a        ,                Arrange  (       a    )      (  a,,[]    )
  | RAssoc  : forall a b c    ,                Arrange  (a,,(b,,c)   )      ((a,,b),,c  )
  | RCossa  : forall a b c    ,                Arrange  ((a,,b),,c   )      ( a,,(b,,c) )
  | RExch   : forall a b      ,                Arrange  (   (b,,a)   )      (  (a,,b)   )
  | RWeak   : forall a        ,                Arrange  (       []   )      (       a   )
  | RCont   : forall a        ,                Arrange  (  (a,,a)    )      (       a   )
  | RLeft   : forall {h}{c} x , Arrange h c -> Arrange  (    x,,h    )      (       x,,c)
  | RRight  : forall {h}{c} x , Arrange h c -> Arrange  (    h,,x    )      (       c,,x)
  | RComp   : forall {a}{b}{c}, Arrange a b -> Arrange b c -> Arrange a c
  .
  
  (* "Arrange" objects are parametric in the type of the leaves of the tree *)
  Definition arrangeMap :
    forall {T} (Σ₁ Σ₂:Tree ??T) {R} (f:T -> R),
      Arrange Σ₁ Σ₂ ->
      Arrange (mapOptionTree f Σ₁) (mapOptionTree f Σ₂).
    intros.
    induction X; simpl.
    apply RId.
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
    eapply RComp; [ apply IHX1 | apply IHX2 ].
    Defined.
  
  (* a frequently-used Arrange - swap the middle two elements of a four-element sequence *)
  Definition arrangeSwapMiddle {T} (a b c d:Tree ??T) :
    Arrange ((a,,b),,(c,,d)) ((a,,c),,(b,,d)).
    eapply RComp.
    apply RCossa.
    eapply RComp.
    eapply RLeft.
    eapply RComp.
    eapply RAssoc.
    eapply RRight.
    apply RExch.
    eapply RComp.
    eapply RLeft.
    eapply RCossa.
    eapply RAssoc.
    Defined.

  (* like RExch, but works on nodes which are an Assoc away from being adjacent *)
  Definition pivotContext {T} a b c : @Arrange T ((a,,b),,c) ((a,,c),,b) :=
    RComp (RComp (RCossa _ _ _) (RLeft a (RExch c b))) (RAssoc _ _ _).

  (* like RExch, but works on nodes which are an Assoc away from being adjacent *)  
  Definition pivotContext' {T} a b c : @Arrange T (a,,(b,,c)) (b,,(a,,c)) :=
    RComp (RComp (RAssoc _ _ _) (RRight c (RExch b a))) (RCossa _ _ _).
  
  Definition copyAndPivotContext {T} a b c : @Arrange T ((a,,b),,(c,,b)) ((a,,c),,b).
    eapply RComp; [ idtac | apply (RLeft (a,,c) (RCont b)) ].
    eapply RComp; [ idtac | apply RCossa ]. 
    eapply RComp; [ idtac | apply (RRight b (pivotContext a b c)) ].
    apply RAssoc.
    Defined.

  (* given any set of TreeFlags on a tree, we can Arrange all of the flagged nodes into the left subtree *)
  Definition arrangePartition :
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

  (* inverse of arrangePartition *)
  Definition arrangeUnPartition :
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

  (* we can decide if a tree consists exclusively of (T_Leaf None)'s *)
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

  (* if a tree is empty, we can Arrange it to [] *)
  Definition arrangeCancelEmptyTree : forall {T}{A}(q:Tree A)(t:Tree ??T),
    t = mapTree (fun _:A => None) q ->
    Arrange t [].
    intros T A q.
    induction q; intros.
      simpl in H.
      rewrite H.
      apply RId.
    simpl in *.
    destruct t; try destruct o; inversion H.
      set (IHq1 _ H1) as x1.
      set (IHq2 _ H2) as x2.
      eapply RComp.
        eapply RRight.
        rewrite <- H1.
        apply x1.
      eapply RComp.
        apply RCanL.
        rewrite <- H2.
        apply x2.
      Defined.

  (* if a tree is empty, we can Arrange it from [] *)
  Definition arrangeUnCancelEmptyTree : forall {T}{A}(q:Tree A)(t:Tree ??T),
    t = mapTree (fun _:A => None) q ->
    Arrange [] t.
    intros T A q.
    induction q; intros.
      simpl in H.
      rewrite H.
      apply RId.
    simpl in *.
    destruct t; try destruct o; inversion H.
      set (IHq1 _ H1) as x1.
      set (IHq2 _ H2) as x2.
      eapply RComp.
        apply RuCanL.
      eapply RComp.
        eapply RRight.
        apply x1.
      eapply RComp.
        eapply RLeft.
        apply x2.
      rewrite H.
      apply RId.
      Defined.

  (* given an Arrange from Σ₁ to Σ₂ and any predicate on tree nodes, we can construct an Arrange from (dropT Σ₁) to (dropT Σ₂) *)
  Lemma arrangeDrop {T} pred
    : forall (Σ₁ Σ₂: Tree ??T), Arrange Σ₁ Σ₂ -> Arrange (dropT (mkFlags pred Σ₁)) (dropT (mkFlags pred Σ₂)).

    refine ((fix arrangeTake t1 t2 (arr:Arrange t1 t2) :=
      match arr as R in Arrange A B return Arrange (dropT (mkFlags pred A)) (dropT (mkFlags pred B)) with
        | RId  a               => let case_RId := tt    in RId _
        | RCanL  a             => let case_RCanL := tt  in _
        | RCanR  a             => let case_RCanR := tt  in _
        | RuCanL a             => let case_RuCanL := tt in _
        | RuCanR a             => let case_RuCanR := tt in _
        | RAssoc a b c         => let case_RAssoc := tt in RAssoc _ _ _
        | RCossa a b c         => let case_RCossa := tt in RCossa _ _ _
        | RExch  a b           => let case_RExch := tt  in RExch _ _
        | RWeak  a             => let case_RWeak := tt  in _
        | RCont  a             => let case_RCont := tt  in _
        | RLeft  a b c r'      => let case_RLeft := tt  in RLeft  _ (arrangeTake _ _ r')
        | RRight a b c r'      => let case_RRight := tt in RRight _ (arrangeTake _ _ r')
        | RComp  a b c r1 r2   => let case_RComp := tt  in RComp (arrangeTake _ _ r1) (arrangeTake _ _ r2)
      end)); clear arrangeTake; intros.

    destruct case_RCanL.
      simpl; destruct (pred None); simpl; apply RCanL.

    destruct case_RCanR.
      simpl; destruct (pred None); simpl; apply RCanR.

    destruct case_RuCanL.
      simpl; destruct (pred None); simpl; apply RuCanL.

    destruct case_RuCanR.
      simpl; destruct (pred None); simpl; apply RuCanR.

    destruct case_RWeak.
      simpl; destruct (pred None); simpl; apply RWeak.

    destruct case_RCont.
      simpl; destruct (pred None); simpl; apply RCont.

      Defined.

  (* given an Arrange from Σ₁ to Σ₂ and any predicate on tree nodes, we can construct an Arrange from (takeT Σ₁) to (takeT Σ₂) *)
  (*
  Lemma arrangeTake {T} pred
    : forall (Σ₁ Σ₂: Tree ??T), Arrange Σ₁ Σ₂ -> Arrange (takeT' (mkFlags pred Σ₁)) (takeT' (mkFlags pred Σ₂)).
    unfold takeT'.
    *)

End NaturalDeductionContext.
