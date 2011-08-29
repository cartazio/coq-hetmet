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
  | AId     : forall a        ,                Arrange           a                  a
  | ACanL   : forall a        ,                Arrange  (    [],,a   )      (       a   )
  | ACanR   : forall a        ,                Arrange  (    a,,[]   )      (       a   )
  | AuCanL  : forall a        ,                Arrange  (       a    )      (  [],,a    )
  | AuCanR  : forall a        ,                Arrange  (       a    )      (  a,,[]    )
  | AAssoc  : forall a b c    ,                Arrange  (a,,(b,,c)   )      ((a,,b),,c  )
  | AuAssoc  : forall a b c    ,                Arrange  ((a,,b),,c   )      ( a,,(b,,c) )
  | AExch   : forall a b      ,                Arrange  (   (b,,a)   )      (  (a,,b)   )
  | AWeak   : forall a        ,                Arrange  (       []   )      (       a   )
  | ACont   : forall a        ,                Arrange  (  (a,,a)    )      (       a   )
  | ALeft   : forall {h}{c} x , Arrange h c -> Arrange  (    x,,h    )      (       x,,c)
  | ARight  : forall {h}{c} x , Arrange h c -> Arrange  (    h,,x    )      (       c,,x)
  | AComp   : forall {a}{b}{c}, Arrange a b -> Arrange b c -> Arrange a c
  .
  
  (* "Arrange" objects are parametric in the type of the leaves of the tree *)
  Definition arrangeMap :
    forall {T} (Σ₁ Σ₂:Tree ??T) {R} (f:T -> R),
      Arrange Σ₁ Σ₂ ->
      Arrange (mapOptionTree f Σ₁) (mapOptionTree f Σ₂).
    intros.
    induction X; simpl.
    apply AId.
    apply ACanL.
    apply ACanR.
    apply AuCanL.
    apply AuCanR.
    apply AAssoc.
    apply AuAssoc.
    apply AExch.
    apply AWeak.
    apply ACont.
    apply ALeft; auto.
    apply ARight; auto.
    eapply AComp; [ apply IHX1 | apply IHX2 ].
    Defined.
  
  (* a frequently-used Arrange - swap the middle two elements of a four-element sequence *)
  Definition arrangeSwapMiddle {T} (a b c d:Tree ??T) :
    Arrange ((a,,b),,(c,,d)) ((a,,c),,(b,,d)).
    eapply AComp.
    apply AuAssoc.
    eapply AComp.
    eapply ALeft.
    eapply AComp.
    eapply AAssoc.
    eapply ARight.
    apply AExch.
    eapply AComp.
    eapply ALeft.
    eapply AuAssoc.
    eapply AAssoc.
    Defined.

  (* like AExch, but works on nodes which are an Assoc away from being adjacent *)
  Definition pivotContext {T} a b c : @Arrange T ((a,,b),,c) ((a,,c),,b) :=
    AComp (AComp (AuAssoc _ _ _) (ALeft a (AExch c b))) (AAssoc _ _ _).

  (* like AExch, but works on nodes which are an Assoc away from being adjacent *)  
  Definition pivotContext' {T} a b c : @Arrange T (a,,(b,,c)) (b,,(a,,c)) :=
    AComp (AComp (AAssoc _ _ _) (ARight c (AExch b a))) (AuAssoc _ _ _).
  
  Definition copyAndPivotContext {T} a b c : @Arrange T ((a,,b),,(c,,b)) ((a,,c),,b).
    eapply AComp; [ idtac | apply (ALeft (a,,c) (ACont b)) ].
    eapply AComp; [ idtac | apply AuAssoc ]. 
    eapply AComp; [ idtac | apply (ARight b (pivotContext a b c)) ].
    apply AAssoc.
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
      apply AuCanL.
      apply AuCanR.
      simpl.
      apply AuCanL.
      simpl in *.
      eapply AComp; [ idtac | apply arrangeSwapMiddle ].
      eapply AComp.
      eapply ALeft.
      apply IHΣ2.
      eapply ARight.
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
      apply ACanL.
      apply ACanR.
      simpl.
      apply ACanL.
      simpl in *.
      eapply AComp; [ apply arrangeSwapMiddle | idtac ].
      eapply AComp.
      eapply ALeft.
      apply IHΣ2.
      eapply ARight.
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
      apply AId.
    simpl in *.
    destruct t; try destruct o; inversion H.
      set (IHq1 _ H1) as x1.
      set (IHq2 _ H2) as x2.
      eapply AComp.
        eapply ARight.
        rewrite <- H1.
        apply x1.
      eapply AComp.
        apply ACanL.
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
      apply AId.
    simpl in *.
    destruct t; try destruct o; inversion H.
      set (IHq1 _ H1) as x1.
      set (IHq2 _ H2) as x2.
      eapply AComp.
        apply AuCanL.
      eapply AComp.
        eapply ARight.
        apply x1.
      eapply AComp.
        eapply ALeft.
        apply x2.
      rewrite H.
      apply AId.
      Defined.

  (* given an Arrange from Σ₁ to Σ₂ and any predicate on tree nodes, we can construct an Arrange from (dropT Σ₁) to (dropT Σ₂) *)
  Lemma arrangeDrop {T} pred
    : forall (Σ₁ Σ₂: Tree ??T), Arrange Σ₁ Σ₂ -> Arrange (dropT (mkFlags pred Σ₁)) (dropT (mkFlags pred Σ₂)).

    refine ((fix arrangeTake t1 t2 (arr:Arrange t1 t2) :=
      match arr as R in Arrange A B return Arrange (dropT (mkFlags pred A)) (dropT (mkFlags pred B)) with
        | AId  a               => let case_AId := tt    in AId _
        | ACanL  a             => let case_ACanL := tt  in _
        | ACanR  a             => let case_ACanR := tt  in _
        | AuCanL a             => let case_AuCanL := tt in _
        | AuCanR a             => let case_AuCanR := tt in _
        | AAssoc a b c         => let case_AAssoc := tt in AAssoc _ _ _
        | AuAssoc a b c         => let case_AuAssoc := tt in AuAssoc _ _ _
        | AExch  a b           => let case_AExch := tt  in AExch _ _
        | AWeak  a             => let case_AWeak := tt  in _
        | ACont  a             => let case_ACont := tt  in _
        | ALeft  a b c r'      => let case_ALeft := tt  in ALeft  _ (arrangeTake _ _ r')
        | ARight a b c r'      => let case_ARight := tt in ARight _ (arrangeTake _ _ r')
        | AComp  a b c r1 r2   => let case_AComp := tt  in AComp (arrangeTake _ _ r1) (arrangeTake _ _ r2)
      end)); clear arrangeTake; intros.

    destruct case_ACanL.
      simpl; destruct (pred None); simpl; apply ACanL.

    destruct case_ACanR.
      simpl; destruct (pred None); simpl; apply ACanR.

    destruct case_AuCanL.
      simpl; destruct (pred None); simpl; apply AuCanL.

    destruct case_AuCanR.
      simpl; destruct (pred None); simpl; apply AuCanR.

    destruct case_AWeak.
      simpl; destruct (pred None); simpl; apply AWeak.

    destruct case_ACont.
      simpl; destruct (pred None); simpl; apply ACont.

      Defined.

  Lemma arrangePullback' {T Q}{f:T->Q}
    : forall (Σ₁:Tree ??Q)(Σ₂:Tree ??Q), Arrange Σ₁ Σ₂ ->
      forall Σ₂', Σ₂ = (mapOptionTree f Σ₂') ->
      { Σ₁' : Tree ??T & prod (Σ₁ = (mapOptionTree f Σ₁')) (Arrange Σ₁' Σ₂') }
      .

    refine ((fix arrangePullback Σ₁ Σ₂ (arr:Arrange Σ₁ Σ₂) {struct arr} :
      forall Σ₂', Σ₂ = (mapOptionTree f Σ₂') ->
      { Σ₁' : Tree ??T & prod (Σ₁ = (mapOptionTree f Σ₁')) (Arrange Σ₁' Σ₂') }
      :=
      match arr as R in Arrange A B return
        forall Σ₂', B = (mapOptionTree f Σ₂') ->
        { Σ₁' : Tree ??T & prod (A = (mapOptionTree f Σ₁')) (Arrange Σ₁' Σ₂') }
        with
        | AId  a               => let case_AId := tt     in _
        | ACanL  a             => let case_ACanL := tt   in _
        | ACanR  a             => let case_ACanR := tt   in _
        | AuCanL a             => let case_AuCanL := tt  in _
        | AuCanR a             => let case_AuCanR := tt  in _
        | AAssoc a b c         => let case_AAssoc := tt  in _
        | AuAssoc a b c        => let case_AuAssoc := tt in _
        | AExch  a b           => let case_AExch := tt   in _
        | AWeak  a             => let case_AWeak := tt   in _
        | ACont  a             => let case_ACont := tt   in _
        | ALeft  a b c r'      => let case_ALeft := tt   in (fun rec       => _) (arrangePullback _ _ r')
        | ARight a b c r'      => let case_ARight := tt  in (fun rec       => _) (arrangePullback _ _ r')
        | AComp  a b c r1 r2   => let case_AComp := tt   in (fun rec1 rec2 => _) (arrangePullback _ _ r1) (arrangePullback _ _ r2)
      end)); clear arrangePullback; intros.

    destruct case_AId.
      exists Σ₂'; split.
      subst.
      reflexivity.
      apply AId.

    destruct case_ACanL.
      exists ([],,Σ₂'); split.
      subst.
      simpl.
      reflexivity.
      apply ACanL.

    destruct case_ACanR.
      exists (Σ₂',,[]); split.
      subst.
      simpl.
      reflexivity.
      apply ACanR.

    destruct case_AuCanL.
      destruct Σ₂'; try destruct o; inversion H; subst.
      eexists; split.
      reflexivity.
      simpl in H.
      inversion H.
      destruct Σ₂'1; try destruct o; inversion H2.
      apply AuCanL.

    destruct case_AuCanR.
      destruct Σ₂'; try destruct o; inversion H; subst.
      eexists; split.
      reflexivity.
      simpl in H.
      inversion H.
      destruct Σ₂'2; try destruct o; inversion H2.
      apply AuCanR.

    destruct case_AAssoc.
      destruct Σ₂'; try destruct o; inversion H; subst.
      destruct Σ₂'1; try destruct o; inversion H; subst.
      rewrite <- mapOptionTree_distributes.
      rewrite <- mapOptionTree_distributes.
      eexists; split.
      reflexivity.
      apply AAssoc.
      
    destruct case_AuAssoc.
      destruct Σ₂'; try destruct o; inversion H; subst.
      destruct Σ₂'2; try destruct o; inversion H; subst.
      rewrite <- mapOptionTree_distributes.
      rewrite <- mapOptionTree_distributes.
      eexists; split.
      reflexivity.
      apply AuAssoc.
      
    destruct case_AExch.
      destruct Σ₂'; try destruct o; inversion H; subst.
      rewrite <- mapOptionTree_distributes.
      eexists; split.
      reflexivity.
      apply AExch.

    destruct case_AWeak.
      exists []; split.
      reflexivity.
      apply AWeak.

    destruct case_ACont.
      exists (Σ₂',,Σ₂').
      subst; split.
      reflexivity.
      apply ACont.

    destruct case_ALeft.
      destruct Σ₂'; try destruct o; inversion H; subst.
      destruct (rec _ (refl_equal _)).
      destruct p.
      rewrite e.
      rewrite <- mapOptionTree_distributes.
      eexists; split.
      reflexivity.
      apply ALeft.
      apply a0.

    destruct case_ARight.
      destruct Σ₂'; try destruct o; inversion H; subst.
      destruct (rec _ (refl_equal _)).
      destruct p.
      rewrite e.
      rewrite <- mapOptionTree_distributes.
      eexists; split.
      reflexivity.
      apply ARight.
      apply a0.

    destruct case_AComp.
      destruct (rec2 _ H).
      destruct p.
      destruct (rec1 _ e).
      destruct p.
      rewrite e0.
      eexists; split.
      reflexivity.
      eapply AComp.
        apply a1.
        apply a0.
        Defined.

  Lemma arrangePullback {T Q}{f:T->Q}
    : forall (Σ₁:Tree ??Q)(Σ₂:Tree ??T), Arrange Σ₁ (mapOptionTree f Σ₂) ->
      { Σ₁' : Tree ??T & prod (Σ₁ = (mapOptionTree f Σ₁')) (Arrange Σ₁' Σ₂) }.
    intros.
    eapply arrangePullback'.
    apply X.
    reflexivity.
    Defined.

  (* given an Arrange from Σ₁ to Σ₂ and any predicate on tree nodes, we can construct an Arrange from (takeT Σ₁) to (takeT Σ₂) *)
  (*
  Lemma arrangePullback {T} pred
    : forall (Σ₁ Σ₂: Tree ??T), Arrange Σ₁ Σ₂ -> Arrange (takeT' (mkFlags pred Σ₁)) (takeT' (mkFlags pred Σ₂)).
    unfold takeT'.
    *)

  (* like Arrange, but without weakening or contraction *)
  Inductive Permutation {T} : Tree ??T -> Tree ??T -> Type :=
  | PId     : forall a        ,                    Permutation           a                  a
  | PCanL   : forall a        ,                    Permutation  (    [],,a   )      (       a   )
  | PCanR   : forall a        ,                    Permutation  (    a,,[]   )      (       a   )
  | PuCanL  : forall a        ,                    Permutation  (       a    )      (  [],,a    )
  | PuCanR  : forall a        ,                    Permutation  (       a    )      (  a,,[]    )
  | PAssoc  : forall a b c    ,                    Permutation  (a,,(b,,c)   )      ((a,,b),,c  )
  | PuAssoc : forall a b c    ,                    Permutation  ((a,,b),,c   )      ( a,,(b,,c) )
  | PExch   : forall a b      ,                    Permutation  (   (b,,a)   )      (  (a,,b)   )
  | PLeft   : forall {h}{c} x , Permutation h c -> Permutation  (    x,,h    )      (       x,,c)
  | PRight  : forall {h}{c} x , Permutation h c -> Permutation  (    h,,x    )      (       c,,x)
  | PComp   : forall {a}{b}{c}, Permutation a b -> Permutation b c -> Permutation a c
  .
  Notation "a ≈ b" := (@Permutation _ a b) (at level 30).
  Notation "a ⊆ b" := (@Arrange _ a b) (at level 30).

  Definition permuteSwapMiddle {T} (a b c d:Tree ??T) :
    ((a,,b),,(c,,d)) ≈ ((a,,c),,(b,,d)).
    eapply PComp.
    apply  PuAssoc.
    eapply PComp.
    eapply PLeft.
    eapply PComp.
    eapply PAssoc.
    eapply PRight.
    apply  PExch.
    eapply PComp.
    eapply PLeft.
    eapply PuAssoc.
    eapply PAssoc.
    Defined.

  Definition permuteMap :
    forall {T} (Σ₁ Σ₂:Tree ??T) {R} (f:T -> R),
      Σ₁ ≈ Σ₂ ->
      (mapOptionTree f Σ₁) ≈ (mapOptionTree f Σ₂).
    intros.
    induction X; simpl.
    apply PId.
    apply PCanL.
    apply PCanR.
    apply PuCanL.
    apply PuCanR.
    apply PAssoc.
    apply PuAssoc.
    apply PExch.
    apply  PLeft; auto.
    apply  PRight; auto.
    eapply PComp; [ apply IHX1 | apply IHX2 ].
    Defined.

  (* given any set of TreeFlags on a tree, we can Arrange all of the flagged nodes into the left subtree *)
  Definition partitionPermutation :
    forall {T} (Σ:Tree ??T) (f:T -> bool),
      Σ ≈ (dropT (mkFlags (liftBoolFunc false f) Σ),,( (dropT (mkFlags (liftBoolFunc false (bnot ○ f)) Σ)))).
    intros.
    induction Σ.
      simpl.
      destruct a.
      simpl.
      destruct (f t); simpl.
      apply PuCanL.
      apply PuCanR.
      simpl.
      apply PuCanL.
      simpl in *.
      eapply PComp; [ idtac | apply permuteSwapMiddle ].
      eapply PComp.
      eapply PLeft.
      apply IHΣ2.
      eapply PRight.
      apply IHΣ1.
      Defined.

  Definition permutationToArrangement {T}{a b:Tree ??T} : a ≈ b -> a ⊆ b.
    intro arr.
    induction arr.
    apply AId.
    apply ACanL.
    apply ACanR.
    apply AuCanL.
    apply AuCanR.
    apply AAssoc.
    apply AuAssoc.
    apply AExch.
    apply ALeft; apply IHarr.
    apply ARight; apply IHarr.
    eapply AComp.
      apply IHarr1.
      apply IHarr2.
      Defined.

  Definition invertPermutation {T}{a b:Tree ??T} : a ≈ b -> b ≈ a.
    intro perm.
    induction perm.
    apply PId.
    apply PuCanL.
    apply PuCanR.
    apply PCanL.
    apply PCanR.
    apply PuAssoc.
    apply PAssoc.
    apply PExch.
    eapply PLeft; apply IHperm.
    eapply PRight; apply IHperm.
    eapply PComp.
      apply IHperm2.
      apply IHperm1.
      Defined.

  (*
  Definition factorArrangementAsPermutation {T} : forall (a b:Tree ??T), a ⊆ b -> { c : _ & (c,,a) ≈ b }.

    refine ((fix factor a b (arr:Arrange a b) :=
      match arr as R in Arrange A B return
        { c : _ & (c,,A) ≈ B }
        with
        | AId  a               => let case_AId := tt    in _
        | ACanL  a             => let case_ACanL := tt  in _
        | ACanR  a             => let case_ACanR := tt  in _
        | AuCanL a             => let case_AuCanL := tt in _
        | AuCanR a             => let case_AuCanR := tt in _
        | AAssoc a b c         => let case_AAssoc := tt in _
        | AuAssoc a b c         => let case_AuAssoc := tt in _
        | AExch  a b           => let case_AExch := tt  in _
        | AWeak  a             => let case_AWeak := tt  in _
        | ACont  a             => let case_ACont := tt  in _
        | ALeft  a b c r'      => let case_ALeft := tt  in (fun r'' => _) (factor _ _ r')
        | ARight a b c r'      => let case_ARight := tt in (fun r'' => _) (factor _ _ r')
        | AComp  a b c r1 r2   => let case_AComp := tt  in (fun r1' r2' => _) (factor _ _ r1) (factor _ _ r2)
      end)); clear factor; intros.

    destruct case_AId.
      exists []. apply PCanL.

    destruct case_ACanL.
      exists [].
      eapply PComp.
      apply PCanL.
      apply PCanL.

    destruct case_ACanR.
      exists [].
      eapply PComp.
      apply PCanL.
      apply PCanR.

    destruct case_AuCanL.
      exists [].
      apply PRight.
      apply PId.

    destruct case_AuCanR.
      exists [].
      apply PExch.

    destruct case_AAssoc.
      exists [].
      eapply PComp.
        eapply PCanL.
        apply PAssoc.

    destruct case_AuAssoc.
      exists [].
      eapply PComp.
        eapply PCanL.
        apply PuAssoc.

    destruct case_AExch.
      exists [].
      eapply PComp.
        eapply PCanL.
        apply PExch.

    destruct case_AWeak.
      exists a0.
      eapply PCanR.

    destruct case_ACont.
      exists [].
      eapply PComp.
      eapply PCanL.
      eapply PComp.
      eapply PLeft.
      eapply  

  Defined.
  *)

End NaturalDeductionContext.
