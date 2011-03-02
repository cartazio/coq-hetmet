(*********************************************************************************************************************************)
(* General: general data structures                                                                                              *)
(*********************************************************************************************************************************)

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Strings.String.
Require Setoid.
Require Import Coq.Lists.List.
Require Import Preamble.
Generalizable All Variables.
Require Import Omega.


Class EqDecidable (T:Type) :=
{ eqd_type           := T
; eqd_dec            :  forall v1 v2:T, sumbool (v1=v2) (not (v1=v2))
; eqd_dec_reflexive  :  forall v, (eqd_dec v v) = (left _ (refl_equal _))
}.
Coercion eqd_type : EqDecidable >-> Sortclass.


(*******************************************************************************)
(* Trees                                                                       *)

Inductive Tree (a:Type) : Type :=
  | T_Leaf   : a -> Tree a
  | T_Branch : Tree a -> Tree a -> Tree a.
Implicit Arguments T_Leaf   [ a ].
Implicit Arguments T_Branch [ a ].

Notation "a ,, b"   := (@T_Branch _ a b)                        : tree_scope.

(* tree-of-option-of-X comes up a lot, so we give it special notations *)
Notation "[ q ]"    := (@T_Leaf (option _) (Some q))            : tree_scope.
Notation "[ ]"      := (@T_Leaf (option _) None)                : tree_scope.
Notation "[]"       := (@T_Leaf (option _) None)                : tree_scope.

Open Scope tree_scope.

Fixpoint mapTree {a b:Type}(f:a->b)(t:@Tree a) : @Tree b :=
  match t with 
    | T_Leaf x     => T_Leaf (f x)
    | T_Branch l r => T_Branch (mapTree f l) (mapTree f r)
  end.
Fixpoint mapOptionTree {a b:Type}(f:a->b)(t:@Tree ??a) : @Tree ??b :=
  match t with 
    | T_Leaf None     => T_Leaf None
    | T_Leaf (Some x) => T_Leaf (Some (f x))
    | T_Branch l r => T_Branch (mapOptionTree f l) (mapOptionTree f r)
  end.
Fixpoint mapTreeAndFlatten {a b:Type}(f:a->@Tree b)(t:@Tree a) : @Tree b :=
  match t with 
    | T_Leaf x        => f x
    | T_Branch l r    => T_Branch (mapTreeAndFlatten f l) (mapTreeAndFlatten f r)
  end.
Fixpoint mapOptionTreeAndFlatten {a b:Type}(f:a->@Tree ??b)(t:@Tree ??a) : @Tree ??b :=
  match t with 
    | T_Leaf None     => []
    | T_Leaf (Some x) => f x
    | T_Branch l r    => T_Branch (mapOptionTreeAndFlatten f l) (mapOptionTreeAndFlatten f r)
  end.
Fixpoint treeReduce {T:Type}{R:Type}(mapLeaf:T->R)(mergeBranches:R->R->R) (t:Tree T) :=
  match t with
  | T_Leaf x => mapLeaf x
  | T_Branch y z => mergeBranches (treeReduce mapLeaf mergeBranches y) (treeReduce mapLeaf mergeBranches z)
  end.
Definition treeDecomposition {D T:Type} (mapLeaf:T->D) (mergeBranches:D->D->D) :=
  forall d:D, { tt:Tree T & d = treeReduce mapLeaf mergeBranches tt }.

Lemma tree_dec_eq :
   forall {Q}(t1 t2:Tree ??Q),
     (forall q1 q2:Q, sumbool (q1=q2) (not (q1=q2))) ->
     sumbool (t1=t2) (not (t1=t2)).
  intro Q.
  intro t1.
  induction t1; intros.

  destruct a; destruct t2.
  destruct o.
  set (X q q0) as X'.
  inversion X'; subst.
  left; auto.
  right; unfold not; intro; apply H. inversion H0; subst. auto.
  right. unfold not; intro; inversion H.
  right. unfold not; intro; inversion H.
  destruct o.
  right. unfold not; intro; inversion H.
  left; auto.
  right. unfold not; intro; inversion H.
  
  destruct t2.
  right. unfold not; intro; inversion H.
  set (IHt1_1 t2_1 X) as X1.
  set (IHt1_2 t2_2 X) as X2.
  destruct X1; destruct X2; subst.
  left; auto.
  
  right.
  unfold not; intro H.
  apply n.
  inversion H; auto.
  
  right.
  unfold not; intro H.
  apply n.
  inversion H; auto.
  
  right.
  unfold not; intro H.
  apply n.
  inversion H; auto.
  Defined.




(*******************************************************************************)
(* Lists                                                                       *)

Notation "a :: b"         := (cons a b)                               : list_scope.
Open Scope list_scope.
Fixpoint leaves {a:Type}(t:Tree (option a)) : list a :=
  match t with
    | (T_Leaf l)     => match l with
                          | None   => nil
                          | Some x => x::nil
                        end
    | (T_Branch l r) => app (leaves l) (leaves r)
  end.
(* weak inverse of "leaves" *)
Fixpoint unleaves {A:Type}(l:list A) : Tree (option A) :=
  match l with
    | nil    => []
    | (a::b) => [a],,(unleaves b)
  end.

(* a map over a list and the conjunction of the results *)
Fixpoint mapProp {A:Type} (f:A->Prop) (l:list A) : Prop :=
  match l with
    | nil => True
    | (a::al) => f a /\ mapProp f al
  end.

Lemma map_id : forall A (l:list A), (map (fun x:A => x) l) = l.
  induction l.
  auto.
  simpl.
  rewrite IHl.
  auto.
  Defined.
Lemma map_app : forall `(f:A->B) l l', map f (app l l') = app (map f l) (map f l').
  intros.
  induction l; auto.
  simpl.
  rewrite IHl.
  auto.
  Defined.
Lemma map_compose : forall A B C (f:A->B)(g:B->C)(l:list A),
  (map (g ○ f) l) = (map g (map f l)).
  intros.
  induction l.
  simpl; auto.
  simpl.
  rewrite IHl.
  auto.
  Defined.
Lemma list_cannot_be_longer_than_itself : forall `(a:A)(b:list A), b = (a::b) -> False.
  intros.
  induction b.
  inversion H.
  inversion H. apply IHb in H2.
  auto.
  Defined.
Lemma list_cannot_be_longer_than_itself' : forall A (b:list A) (a c:A), b = (a::c::b) -> False.
  induction b.
  intros; inversion H.
  intros.
  inversion H.
  apply IHb in H2.
  auto.
  Defined.

Lemma mapOptionTree_on_nil : forall `(f:A->B) h, [] = mapOptionTree f h -> h=[].
  intros.
  destruct h.
  destruct o. inversion H.
  auto.
  inversion H.
  Defined.

Lemma mapOptionTree_comp a b c (f:a->b) (g:b->c) q : (mapOptionTree g (mapOptionTree f q)) = mapOptionTree (g ○ f) q.
  induction q.
    destruct a0; simpl.
    reflexivity.
    reflexivity.
    simpl.
    rewrite IHq1.
    rewrite IHq2.
    reflexivity.
  Qed.

(* handy facts: map preserves the length of a list *)
Lemma map_on_nil : forall A B (s1:list A) (f:A->B), nil = map f s1 -> s1=nil.
  intros.
  induction s1.
  auto.
  assert False.
  simpl in H.
  inversion H.
  inversion H0.
  Defined.
Lemma map_on_singleton : forall A B (f:A->B) x (s1:list A), (cons x nil) = map f s1 -> { y : A & s1=(cons y nil) & (f y)=x }.
  induction s1.
  intros.
  simpl in H; assert False. inversion H. inversion H0.
  clear IHs1.
  intros.
  exists a.
  simpl in H.
  assert (s1=nil).
    inversion H. apply map_on_nil in H2. auto.
  subst.
  auto.
  assert (s1=nil).
    inversion H. apply map_on_nil in H2. auto.
  subst.
  simpl in H.
  inversion H. auto.
  Defined.

Lemma map_on_doubleton : forall A B (f:A->B) x y (s1:list A), ((x::y::nil) = map f s1) ->
  { z : A*A & s1=((fst z)::(snd z)::nil) & (f (fst z))=x /\ (f (snd z))=y }.
  intros.
  destruct s1.
  inversion H.
  destruct s1.
  inversion H.
  destruct s1.
  inversion H.
  exists (a,a0); auto.
  simpl in H.
  inversion H.
  Defined.


Lemma mapTree_compose : forall A B C (f:A->B)(g:B->C)(l:Tree A),
  (mapTree (g ○ f) l) = (mapTree g (mapTree f l)).
  induction l.
    reflexivity.
    simpl.
    rewrite IHl1.
    rewrite IHl2.
    reflexivity.
    Defined.

Lemma lmap_compose : forall A B C (f:A->B)(g:B->C)(l:list A),
  (map (g ○ f) l) = (map g (map f l)).
  intros.
  induction l.
  simpl; auto.
  simpl.
  rewrite IHl.
  auto.
  Defined.

(* sends a::b::c::nil to [[[[],,c],,b],,a] *)
Fixpoint unleaves' {A:Type}(l:list A) : Tree (option A) :=
  match l with
    | nil    => []
    | (a::b) => (unleaves' b),,[a]
  end.

(* sends a::b::c::nil to [[[[],,c],,b],,a] *)
Fixpoint unleaves'' {A:Type}(l:list ??A) : Tree ??A :=
  match l with
    | nil    => []
    | (a::b) => (unleaves'' b),,(T_Leaf a)
  end.

Fixpoint filter {T:Type}(l:list ??T) : list T :=
  match l with
    | nil => nil
    | (None::b) => filter b
    | ((Some x)::b) => x::(filter b)
  end.

Inductive distinct {T:Type} : list T -> Prop :=
| distinct_nil  : distinct nil
| distinct_cons : forall a ax, (@In _ a ax -> False) -> distinct ax -> distinct (a::ax).

Lemma map_preserves_length {A}{B}(f:A->B)(l:list A) : (length l) = (length (map f l)).
  induction l; auto.
  simpl.
  omega.
  Qed.

(* decidable quality on a list of elements which have decidable equality *)
Definition list_eq_dec : forall {T:Type}(l1 l2:list T)(dec:forall t1 t2:T, sumbool (eq t1 t2) (not (eq t1 t2))),
  sumbool (eq l1 l2) (not (eq l1 l2)).
  intro T.
  intro l1.
  induction l1; intros.
    destruct l2.
    left; reflexivity.
    right; intro H; inversion H.
  destruct l2 as [| b l2].
    right; intro H; inversion H.
  set (IHl1 l2 dec) as eqx.
    destruct eqx.
    subst.
    set (dec a b) as eqy.
    destruct eqy.
      subst.
      left; reflexivity.
      right. intro. inversion H. subst. apply n. auto.
    right.
      intro.
      inversion H.
      apply n.
      auto.
      Defined.




(*******************************************************************************)
(* Length-Indexed Lists                                                        *)

Inductive vec (A:Type) : nat -> Type :=
| vec_nil  : vec A 0
| vec_cons : forall n, A -> vec A n -> vec A (S n).

Fixpoint vec2list {n:nat}{t:Type}(v:vec t n) : list t :=
  match v with
    | vec_nil => nil
    | vec_cons n a va => a::(vec2list va)
  end.

Require Import Omega.
Definition vec_get : forall {T:Type}{l:nat}(v:vec T l)(n:nat)(pf:lt n l), T.
  intro T.
  intro len.
  intro v.
  induction v; intros.
    assert False.
    inversion pf.
    inversion H.
  rename n into len.
    destruct n0 as [|n].
    exact a.
    apply (IHv n).
    omega.
    Defined.

Definition vec_zip {n:nat}{A B:Type}(va:vec A n)(vb:vec B n) : vec (A*B) n.
  induction n.
  apply vec_nil.
  inversion va; subst.
  inversion vb; subst.
  apply vec_cons; auto.
  Defined.  

Definition vec_map {n:nat}{A B:Type}(f:A->B)(v:vec A n) : vec B n.
  induction n.
  apply vec_nil.
  inversion v; subst.
  apply vec_cons; auto.
  Defined.

Fixpoint vec_In {A:Type} {n:nat} (a:A) (l:vec A n) : Prop :=
  match l with
    | vec_nil         => False
    | vec_cons _ n m  => (n = a) \/ vec_In a m
  end.
Implicit Arguments vec_nil  [ A   ].
Implicit Arguments vec_cons [ A n ].

Definition append_vec {n:nat}{T:Type}(v:vec T n)(t:T) : vec T (S n).
  induction n.
  apply (vec_cons t vec_nil).
  apply vec_cons; auto.
  Defined.

Definition list2vec {T:Type}(l:list T) : vec T (length l).
  induction l.
  apply vec_nil.
  apply vec_cons; auto.
  Defined.

Definition vec_head {n:nat}{T}(v:vec T (S n)) : T.
  inversion v;  auto.
  Defined.
Definition vec_tail {n:nat}{T}(v:vec T (S n)) : vec T n.
  inversion v;  auto.
  Defined.

Lemma vec_chop {T}{l1 l2:list T}{Q}(v:vec Q (length (app l1 l2))) : vec Q (length l1).
  induction l1.
  apply vec_nil.
  apply vec_cons.
  simpl in *.
  inversion v; subst; auto.
  apply IHl1.
  inversion v; subst; auto.
  Defined.

Lemma vec_chop' {T}{l1 l2:list T}{Q}(v:vec Q (length (app l1 l2))) : vec Q (length l2).
  induction l1.
  apply v.
  simpl in *.
  apply IHl1; clear IHl1.
  inversion v; subst; auto.
  Defined.

Notation "a ::: b" := (@vec_cons _ _ a b) (at level 20).



(*******************************************************************************)
(* Shaped Trees                                                                *)

(* a ShapedTree is a tree indexed by the shape (but not the leaf values) of another tree; isomorphic to (ITree (fun _ => Q)) *)
Inductive ShapedTree {T:Type}(Q:Type) : Tree ??T -> Type :=
| st_nil    : @ShapedTree T Q []
| st_leaf   : forall {t}, Q -> @ShapedTree T Q [t]
| st_branch : forall {t1}{t2}, @ShapedTree T Q t1 -> @ShapedTree T Q t2 -> @ShapedTree T Q (t1,,t2).

Fixpoint unshape {T:Type}{Q:Type}{idx:Tree ??T}(st:@ShapedTree T Q idx) : Tree ??Q :=
match st with
| st_nil => []
| st_leaf _ q => [q]
| st_branch _ _ b1 b2 => (unshape b1),,(unshape b2)
end.

Definition mapShapedTree {T}{idx:Tree ??T}{V}{Q}(f:V->Q)(st:ShapedTree V idx) : ShapedTree Q idx.
  induction st.
  apply st_nil.
  apply st_leaf. apply f. apply q.
  apply st_branch; auto.
  Defined.

Definition zip_shapedTrees {T:Type}{Q1 Q2:Type}{idx:Tree ??T} 
   (st1:ShapedTree Q1 idx)(st2:ShapedTree Q2 idx) : ShapedTree (Q1*Q2) idx.
  induction idx.
    destruct a.
    apply st_leaf; auto.
    inversion st1.
    inversion st2.
    auto.
    apply st_nil.
    apply st_branch; auto.
    inversion st1; subst; apply IHidx1; auto.
    inversion st2; subst; auto.
    inversion st2; subst; apply IHidx2; auto.
    inversion st1; subst; auto.
  Defined.

Definition build_shapedTree {T:Type}(idx:Tree ??T){Q:Type}(f:T->Q) : ShapedTree Q idx.
  induction idx.
  destruct a.
  apply st_leaf; auto.
  apply st_nil.
  apply st_branch; auto.
  Defined.

Lemma unshape_map : forall {Q}{b}(f:Q->b){T}{idx:Tree ??T}(t:ShapedTree Q idx),
   mapOptionTree f (unshape t) = unshape (mapShapedTree f t).
  intros.
  induction t; auto.
  simpl.
  rewrite IHt1.
  rewrite IHt2.
  reflexivity.
  Qed.




(*******************************************************************************)
(* Type-Indexed Lists                                                          *)

(* an indexed list *)
Inductive IList (I:Type)(F:I->Type) : list I -> Type :=
| INil      :                                       IList I F nil
| ICons     :   forall i is, F i -> IList I F is -> IList I F (i::is).
Implicit Arguments INil [ I F ].
Implicit Arguments ICons [ I F ].

(* a tree indexed by a (Tree (option X)) *)
Inductive ITree (I:Type)(F:I->Type) : Tree ??I -> Type :=
| INone      :                                ITree I F []
| ILeaf      :  forall       i:     I, F i -> ITree I F [i]
| IBranch    :  forall it1 it2:Tree ??I, ITree I F it1 -> ITree I F it2 -> ITree I F (it1,,it2).
Implicit Arguments INil    [ I F ].
Implicit Arguments ILeaf   [ I F ].
Implicit Arguments IBranch [ I F ].




(*******************************************************************************)
(* Extensional equality on functions                                           *)

Definition extensionality := fun (t1 t2:Type) => (fun (f:t1->t2) g => forall x:t1, (f x)=(g x)).
Hint Transparent extensionality.
Instance extensionality_Equivalence : forall t1 t2, Equivalence (extensionality t1 t2).
  intros; apply Build_Equivalence;
    intros; compute; intros; auto.
    rewrite H; rewrite H0; auto.
  Defined.
  Add Parametric Morphism (A B C:Type) : (fun f g => g ○ f)
  with signature (extensionality A B ==> extensionality B C ==> extensionality A C) as parametric_morphism_extensionality.
  unfold extensionality; intros; rewrite (H x1); rewrite (H0 (y x1)); auto.
  Defined.
Lemma extensionality_composes : forall t1 t2 t3 (f f':t1->t2) (g g':t2->t3),
  (extensionality _ _ f f') ->
  (extensionality _ _ g g') ->
  (extensionality _ _ (g ○ f) (g' ○ f')).
  intros.
  unfold extensionality.
  unfold extensionality in H.
  unfold extensionality in H0.
  intros.
  rewrite H.
  rewrite H0.
  auto.
  Qed.






(* the Error monad *)
Inductive OrError (T:Type) :=
| Error : forall error_message:string, OrError T
| OK    : T      -> OrError T.
Notation "??? T" := (OrError T) (at level 10).
Implicit Arguments Error [T].
Implicit Arguments OK [T].

Definition orErrorBind {T:Type} (oe:OrError T) {Q:Type} (f:T -> OrError Q) :=
  match oe with
    | Error s => Error s
    | OK    t => f t
  end.
Notation "a >>= b" := (@orErrorBind _ a _ b) (at level 20).

Fixpoint list2vecOrError {T}(l:list T)(n:nat) : ???(vec T n) :=
  match n as N return ???(vec _ N) with
    | O => match l with
             | nil => OK vec_nil
             | _   => Error "list2vecOrError: list was too long"
           end
    | S n' => match l with
                | nil   => Error "list2vecOrError: list was too short"
                | t::l' => list2vecOrError l' n' >>= fun l'' => OK (vec_cons t l'')
              end
  end.

Inductive Indexed {T:Type}(f:T -> Type) : ???T -> Type :=
| Indexed_Error : forall error_message:string, Indexed f (Error error_message)
| Indexed_OK    : forall t, f t -> Indexed f (OK t)
.
Ltac xauto := try apply Indexed_Error; try apply Indexed_OK.






(* for a type with decidable equality, we can maintain lists of distinct elements *)
Section DistinctList.
  Context `{V:EqDecidable}.

  Fixpoint addToDistinctList (cv:V)(cvl:list V) :=
  match cvl with
  | nil       => cv::nil
  | cv'::cvl' => if eqd_dec cv cv' then cvl' else cv'::(addToDistinctList cv cvl')
  end.
  
  Fixpoint removeFromDistinctList (cv:V)(cvl:list V) :=
  match cvl with
  | nil => nil
  | cv'::cvl' => if eqd_dec cv cv' then removeFromDistinctList cv cvl' else cv'::(removeFromDistinctList cv cvl')
  end.
  
  Fixpoint removeFromDistinctList' (cvrem:list V)(cvl:list V) :=
  match cvrem with
  | nil         => cvl
  | rem::cvrem' => removeFromDistinctList rem (removeFromDistinctList' cvrem' cvl)
  end.
  
  Fixpoint mergeDistinctLists (cvl1:list V)(cvl2:list V) :=
  match cvl1 with
  | nil       => cvl2
  | cv'::cvl' => mergeDistinctLists cvl' (addToDistinctList cv' cvl2)
  end.
End DistinctList.
