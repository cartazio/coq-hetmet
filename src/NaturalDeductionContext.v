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
  
  (* a frequently-used Arrange *)
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

  Definition pivotContext {T} a b c : @Arrange T ((a,,b),,c) ((a,,c),,b) :=
    RComp (RComp (RCossa _ _ _) (RLeft a (RExch c b))) (RAssoc _ _ _).
  
  Definition pivotContext' {T} a b c : @Arrange T (a,,(b,,c)) (b,,(a,,c)) :=
    RComp (RComp (RAssoc _ _ _) (RRight c (RExch b a))) (RCossa _ _ _).
  
  Definition copyAndPivotContext {T} a b c : @Arrange T ((a,,b),,(c,,b)) ((a,,c),,b).
    eapply RComp; [ idtac | apply (RLeft (a,,c) (RCont b)) ].
    eapply RComp; [ idtac | apply RCossa ]. 
    eapply RComp; [ idtac | apply (RRight b (pivotContext a b c)) ].
    apply RAssoc.
    Defined.

End NaturalDeductionContext.
