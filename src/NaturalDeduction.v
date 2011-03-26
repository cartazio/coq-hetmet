(*********************************************************************************************************************************)
(* NaturalDeduction:                                                                                                             *)
(*                                                                                                                               *)
(*   Structurally explicit natural deduction proofs.                                                                             *)
(*                                                                                                                               *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

(*
 * IMPORTANT!!!
 *
 * Unlike most formalizations, this library offers TWO different ways
 * to represent a natural deduction proof.  To demonstrate this,
 * consider the signature of the propositional calculus:
 *
 *   Variable  PropositionalVariable : Type.
 *
 *   Inductive Formula : Prop :=
 *   | formula_var : PropositionalVariable -> Formula   (* every propositional variable is a formula *)
 *   | formula_and :   Formula ->  Formula -> Formula   (* the conjunction of any two formulae is a formula *)
 *   | formula_or  :   Formula ->  Formula -> Formula   (* the disjunction of any two formulae is a formula *)
 *
 * And couple this with the theory of conjunction and disjunction:
 * φ\/ψ is true if either φ is true or ψ is true, and φ/\ψ is true
 * if both φ and ψ are true.
 *
 * 1) Structurally implicit proofs
 *
 *    This is what you would call the "usual" representation –- it's
 *    what most people learn when they first start programming in Coq:
 *
 *    Inductive IsTrue : Formula -> Prop :=
 *    | IsTrue_or1 : forall f1 f2, IsTrue f1 ->              IsTrue (formula_or  f1 f2) 
 *    | IsTrue_or2 : forall f1 f2,              IsTrue f2 -> IsTrue (formula_or  f1 f2) 
 *    | IsTrue_and : forall f1 f2, IsTrue f2 -> IsTrue f2 -> IsTrue (formula_and f1 f2) 
 *
 *    Here each judgment (such as "φ is true") is represented by a Coq
 *    type; furthermore:
 *
 *       1. A proof of a judgment is any inhabitant of that Coq type.
 *
 *       2. A proof of a judgment "J2" from hypothesis judgment "J1"
 *          is any Coq function from the Coq type for J1 to the Coq
 *          type for J2; Composition of (hypothetical) proofs is
 *          represented by composition of Coq functions.
 *
 *       3. A pair of judgments is represented by their product (Coq
 *          type [prod]) in Coq; a pair of proofs is represented by
 *          their pair (Coq function [pair]) in Coq.
 *
 *       4. Duplication of hypotheses is represented by the Coq
 *          function (fun x => (x,x)).  Dereliction of hypotheses is
 *          represented by the coq function (fun (x,y) => x) or (fun
 *          (x,y) => y).  Exchange of the order of hypotheses is
 *          represented by the Coq function (fun (x,y) => (y,x)).
 *
 *    The above can be done using lists instead of tuples.
 *
 *    The advantage of this approach is that it requires a minimum
 *    amount of syntax, and takes maximum advantage of Coq's
 *    automation facilities.
 *
 *    The disadvantage is that one cannot reason about proof-theoretic
 *    properties *generically* across different signatures and
 *    theories.  Each signature has its own type of judgments, and
 *    each theory has its own type of proofs.  In the present
 *    development we will want to prove –– in this generic manner --
 *    that various classes of natural deduction calculi form various
 *    kinds of categories.  So we will need this ability to reason
 *    about proofs independently of the type used to represent
 *    judgments and (more importantly) of the set of basic inference
 *    rules.
 *
 * 2) Structurally explicit proofs
 *
 *    Structurally explicit proofs are formalized in this file
 *    (NaturalDeduction.v) and are designed specifically in order to
 *    circumvent the problem in the previous paragraph.
 *
 *)

(*
 * REGARDING LISTS versus TREES:
 *
 * You'll notice that this formalization uses (Tree (option A)) in a
 * lot of places where you might find (list A) more natural.  If this
 * bothers you, see the end of the file for the technical reasons why.
 * In short, it lets us avoid having to mess about with JMEq or EqDep,
 * which are not as well-supported by the Coq core as the theory of
 * CiC proper.
 *)

Section Natural_Deduction.

  (* any Coq Type may be used as the set of judgments *)
  Context {Judgment : Type}.

  (* any Coq Type –- indexed by the hypothesis and conclusion judgments -- may be used as the set of basic inference rules *)
  Context {Rule     : forall (hypotheses:Tree ??Judgment)(conclusion:Tree ??Judgment), Type}.

  (*
   *  This type represents a valid Natural Deduction proof from a list
   *  (tree) of hypotheses; the notation H/⋯⋯/C is meant to look like
   *  a proof tree with the middle missing if you tilt your head to
   *  the left (yeah, I know it's a stretch).  Note also that this
   *  type is capable of representing proofs with multiple
   *  conclusions, whereas a Rule may have only one conclusion.
   *) 
  Inductive ND :
    forall hypotheses:Tree ??Judgment,
      forall conclusions:Tree ??Judgment,
        Type :=

    (* natural deduction: you may infer anything from itself -- "identity proof" *)
    | nd_id0    :             [   ] /⋯⋯/ [   ]
    | nd_id1    : forall  h,  [ h ] /⋯⋯/ [ h ]
  
    (* natural deduction: you may discard conclusions *)
    | nd_weak   : forall  h,  [ h ] /⋯⋯/ [   ]
  
    (* natural deduction: you may duplicate conclusions *)
    | nd_copy   : forall  h,    h   /⋯⋯/ (h,,h)
  
    (* natural deduction: you may write two proof trees side by side on a piece of paper -- "proof product" *)
    | nd_prod : forall {h1 h2 c1 c2}
       (pf1: h1       /⋯⋯/ c1      )
       (pf2:       h2 /⋯⋯/       c2),
       (     h1 ,, h2 /⋯⋯/ c1 ,, c2)
  
    (* natural deduction: given a proof of every hypothesis, you may discharge them -- "proof composition" *)
    | nd_comp :
      forall {h x c}
      `(pf1: h /⋯⋯/ x)
      `(pf2: x /⋯⋯/ c),
       (     h /⋯⋯/ c)
  
    (* structural rules on lists of judgments *)
    | nd_cancell : forall {a},       [] ,, a /⋯⋯/ a
    | nd_cancelr : forall {a},       a ,, [] /⋯⋯/ a
    | nd_llecnac : forall {a},             a /⋯⋯/ [] ,, a
    | nd_rlecnac : forall {a},             a /⋯⋯/ a ,, []
    | nd_assoc   : forall {a b c}, (a,,b),,c /⋯⋯/ a,,(b,,c)
    | nd_cossa   : forall {a b c}, a,,(b,,c) /⋯⋯/ (a,,b),,c

    (* any Rule by itself counts as a proof *)
    | nd_rule    : forall {h c} (r:Rule h c), h /⋯⋯/ c
  
    where  "H /⋯⋯/ C" := (ND H C).

    Notation "H /⋯⋯/ C" := (ND H C) : pf_scope.
    Notation "a ;; b"   := (nd_comp a b) : nd_scope.
    Notation "a ** b"   := (nd_prod a b) : nd_scope.
    Open Scope nd_scope.
    Open Scope pf_scope.

  (* a proof is "structural" iff it does not contain any invocations of nd_rule *)
  Inductive Structural : forall {h c}, h /⋯⋯/ c -> Prop :=
  | nd_structural_id0     :                                                                            Structural nd_id0
  | nd_structural_id1     : forall h,                                                                  Structural (nd_id1 h)
  | nd_structural_weak    : forall h,                                                                  Structural (nd_weak h)
  | nd_structural_copy    : forall h,                                                                  Structural (nd_copy h)
  | nd_structural_prod    : forall `(pf1:h1/⋯⋯/c1)`(pf2:h2/⋯⋯/c2), Structural pf1 -> Structural pf2 -> Structural (pf1**pf2)
  | nd_structural_comp    : forall `(pf1:h1/⋯⋯/x) `(pf2: x/⋯⋯/c2), Structural pf1 -> Structural pf2 -> Structural (pf1;;pf2)
  | nd_structural_cancell : forall {a},                                                                Structural (@nd_cancell a)
  | nd_structural_cancelr : forall {a},                                                                Structural (@nd_cancelr a)
  | nd_structural_llecnac : forall {a},                                                                Structural (@nd_llecnac a)
  | nd_structural_rlecnac : forall {a},                                                                Structural (@nd_rlecnac a)
  | nd_structural_assoc   : forall {a b c},                                                            Structural (@nd_assoc a b c)
  | nd_structural_cossa   : forall {a b c},                                                            Structural (@nd_cossa a b c)
  .

  (* multi-judgment generalization of nd_id0 and nd_id1; making nd_id0/nd_id1 primitive and deriving all other *)
  Fixpoint nd_id (sl:Tree ??Judgment) : sl /⋯⋯/ sl :=
    match sl with
      | T_Leaf None      => nd_id0
      | T_Leaf (Some x)  => nd_id1 x
      | T_Branch a b     => nd_prod (nd_id a) (nd_id b)
    end.

  Fixpoint nd_weak' (sl:Tree ??Judgment) : sl /⋯⋯/ [] :=
    match sl as SL return SL /⋯⋯/ [] with
      | T_Leaf None      => nd_id0
      | T_Leaf (Some x)  => nd_weak x
      | T_Branch a b     => nd_prod (nd_weak' a) (nd_weak' b) ;; nd_cancelr
    end.

  Hint Constructors Structural.
  Lemma nd_id_structural : forall sl, Structural (nd_id sl).
    intros.
    induction sl; simpl; auto.
    destruct a; auto.
    Defined.

  Lemma weak'_structural : forall a, Structural (nd_weak' a).
    intros.
    induction a.
    destruct a; auto.
    simpl.
    auto.
    simpl.
    auto.
    Qed.

  (* An equivalence relation on proofs which is sensitive only to the logical content of the proof -- insensitive to
   * structural variations  *)
  Class ND_Relation :=
  { ndr_eqv                  : forall {h c  }, h /⋯⋯/ c -> h /⋯⋯/ c -> Prop where "pf1 === pf2" := (@ndr_eqv _ _  pf1 pf2)
  ; ndr_eqv_equivalence      : forall h c, Equivalence (@ndr_eqv h c)

  (* the relation must respect composition, be associative wrt composition, and be left and right neutral wrt the identity proof *)
  ; ndr_comp_respects        : forall {a b c}(f f':a/⋯⋯/b)(g g':b/⋯⋯/c),      f === f' -> g === g' -> f;;g === f';;g'
  ; ndr_comp_associativity   : forall `(f:a/⋯⋯/b)`(g:b/⋯⋯/c)`(h:c/⋯⋯/d),                         (f;;g);;h === f;;(g;;h)
  ; ndr_comp_left_identity   : forall `(f:a/⋯⋯/c),                                          nd_id _ ;; f   === f
  ; ndr_comp_right_identity  : forall `(f:a/⋯⋯/c),                                          f ;; nd_id _   === f

  (* the relation must respect products, be associative wrt products, and be left and right neutral wrt the identity proof *)
  ; ndr_prod_respects        : forall {a b c d}(f f':a/⋯⋯/b)(g g':c/⋯⋯/d),     f===f' -> g===g' ->    f**g === f'**g'
  ; ndr_prod_associativity   : forall `(f:a/⋯⋯/a')`(g:b/⋯⋯/b')`(h:c/⋯⋯/c'),       (f**g)**h === nd_assoc ;; f**(g**h) ;; nd_cossa
  ; ndr_prod_left_identity   : forall `(f:a/⋯⋯/b),                       (nd_id0 ** f ) === nd_cancell ;; f ;; nd_llecnac
  ; ndr_prod_right_identity  : forall `(f:a/⋯⋯/b),                       (f ** nd_id0)  === nd_cancelr ;; f ;; nd_rlecnac

  (* products and composition must distribute over each other *)
  ; ndr_prod_preserves_comp  : forall `(f:a/⋯⋯/b)`(f':a'/⋯⋯/b')`(g:b/⋯⋯/c)`(g':b'/⋯⋯/c'), (f;;g)**(f';;g') === (f**f');;(g**g')

  (* products and duplication must distribute over each other *)
  ; ndr_prod_preserves_copy  : forall `(f:a/⋯⋯/b),                                        nd_copy a;; f**f === f ;; nd_copy b

  (* any two _structural_ proofs with the same hypotheses/conclusions must be considered equal *)
  ; ndr_structural_indistinguishable : forall `(f:a/⋯⋯/b)(g:a/⋯⋯/b), Structural f -> Structural g -> f===g

  (* any two proofs of nothing are "equally good" *)
  ; ndr_void_proofs_irrelevant : forall `(f:a/⋯⋯/[])(g:a/⋯⋯/[]), f === g
  }.

  (* 
   * Single-conclusion proofs; this is an alternate representation
   * where each inference has only a single conclusion.  These have
   * worse compositionality properties than ND's, but are easier to
   * emit as LaTeX code.
   *)
  Inductive SCND : Tree ??Judgment -> Tree ??Judgment -> Type :=
  | scnd_comp   : forall ht ct c , SCND ht ct -> Rule ct [c] -> SCND ht [c]
  | scnd_weak   : forall c       , SCND c  []
  | scnd_leaf   : forall ht c    , SCND ht [c]  -> SCND ht [c]
  | scnd_branch : forall ht c1 c2, SCND ht c1 -> SCND ht c2 -> SCND ht (c1,,c2)
  .
  Hint Constructors SCND.

  (* Any ND whose primitive Rules have at most one conclusion (note that nd_prod is allowed!) can be turned into an SCND. *)
  Definition mkSCND (all_rules_one_conclusion : forall h c1 c2, Rule h (c1,,c2) -> False)
    : forall h x c,  ND x c -> SCND h x -> SCND h c.
    intros h x c nd.
    induction nd; intro k.
      apply k.
      apply k.
      apply scnd_weak.
      eapply scnd_branch; apply k.
      inversion k; subst.
        apply (scnd_branch _ _ _ (IHnd1 X) (IHnd2 X0)).
      apply IHnd2.
        apply IHnd1.
        apply k.
      inversion k; subst; auto.
      inversion k; subst; auto.
      apply scnd_branch; auto.
      apply scnd_branch; auto.
      inversion k; subst; inversion X; subst; auto.
      inversion k; subst; inversion X0; subst; auto.
      destruct c.
        destruct o.
        apply scnd_leaf. eapply scnd_comp. apply k. apply r.
        apply scnd_weak.
        set (all_rules_one_conclusion _ _ _ r) as bogus.
          inversion bogus.
          Defined.

  (* a "ClosedND" is a proof with no open hypotheses and no multi-conclusion rules *)
  Inductive ClosedND : Tree ??Judgment -> Type :=
  | cnd_weak   : ClosedND []
  | cnd_rule   : forall h c    , ClosedND h  -> Rule h c    -> ClosedND c
  | cnd_branch : forall   c1 c2, ClosedND c1 -> ClosedND c2 -> ClosedND (c1,,c2)
  .

  (* we can turn an SCND without hypotheses into a ClosedND *)
  Definition closedFromSCND h c (pn2:SCND h c)(cnd:ClosedND h) : ClosedND c.
  refine ((fix closedFromPnodes h c (pn2:SCND h c)(cnd:ClosedND h) {struct pn2} := 
    (match pn2 in SCND H C return H=h -> C=c -> _  with
      | scnd_weak   c                 => let case_weak := tt in _
      | scnd_leaf   ht z pn'          => let case_leaf := tt in let qq := closedFromPnodes _ _ pn' in _
      | scnd_comp  ht ct c pn' rule   => let case_comp := tt in let qq := closedFromPnodes _ _ pn' in _
      | scnd_branch ht c1 c2 pn' pn'' => let case_branch := tt in
                                        let q1 := closedFromPnodes _ _ pn' in 
                                        let q2 := closedFromPnodes _ _ pn'' in _

    end (refl_equal _) (refl_equal _))) h c pn2 cnd).

  destruct case_comp.
    intros.
    clear pn2.
    apply (cnd_rule ct).
    apply qq.
    subst.
    apply cnd0.
    apply rule.

  destruct case_weak.
    intros; subst.
    apply cnd_weak.

  destruct case_leaf.
    intros.
    apply qq.
    subst.
    apply cnd0.

  destruct case_branch.
    intros.
    apply cnd_branch.
    apply q1. subst. apply cnd0.
    apply q2. subst. apply cnd0.
    Defined.

  (* undo the above *)
  Fixpoint closedNDtoNormalND {c}(cnd:ClosedND c) : ND [] c :=
  match cnd in ClosedND C return ND [] C with
  | cnd_weak                   => nd_id0
  | cnd_rule   h c cndh rhc    => closedNDtoNormalND cndh ;; nd_rule rhc
  | cnd_branch c1 c2 cnd1 cnd2 => nd_llecnac ;; nd_prod (closedNDtoNormalND cnd1) (closedNDtoNormalND cnd2)
  end.

  Close Scope nd_scope.
  Open Scope pf_scope.

End Natural_Deduction.

Implicit Arguments ND [ Judgment ].
Hint Constructors Structural.
Hint Extern 1 => apply nd_id_structural.
Hint Extern 1 => apply ndr_structural_indistinguishable.

(* This first notation gets its own scope because it can be confusing when we're working with multiple different kinds
 * of proofs.  When only one kind of proof is in use, it's quite helpful though. *)
Notation "H /⋯⋯/ C" := (@ND _ _ H C)             : pf_scope.
Notation "a ;; b"   := (nd_comp a b)             : nd_scope.
Notation "a ** b"   := (nd_prod a b)             : nd_scope.
Notation "[# a #]"  := (nd_rule a)               : nd_scope.
Notation "a === b"  := (@ndr_eqv _ _ _ _ _ a b)  : nd_scope.

(* enable setoid rewriting *)
Open Scope nd_scope.
Open Scope pf_scope.

Add Parametric Relation {jt rt ndr h c} : (h/⋯⋯/c) (@ndr_eqv jt rt ndr h c)
  reflexivity proved by  (@Equivalence_Reflexive  _ _ (ndr_eqv_equivalence h c))
  symmetry proved by     (@Equivalence_Symmetric  _ _ (ndr_eqv_equivalence h c))
  transitivity proved by (@Equivalence_Transitive _ _ (ndr_eqv_equivalence h c))
    as parametric_relation_ndr_eqv.
  Add Parametric Morphism {jt rt ndr h x c} : (@nd_comp jt rt h x c)
  with signature ((ndr_eqv(ND_Relation:=ndr)) ==> (ndr_eqv(ND_Relation:=ndr)) ==> (ndr_eqv(ND_Relation:=ndr)))
    as parametric_morphism_nd_comp.
    intros; apply ndr_comp_respects; auto.
    Defined.
  Add Parametric Morphism {jt rt ndr a b c d} : (@nd_prod jt rt a b c d)
  with signature ((ndr_eqv(ND_Relation:=ndr)) ==> (ndr_eqv(ND_Relation:=ndr)) ==> (ndr_eqv(ND_Relation:=ndr)))
    as parametric_morphism_nd_prod.
    intros; apply ndr_prod_respects; auto.
    Defined.

(* a generalization of the procedure used to build (nd_id n) from nd_id0 and nd_id1 *)
Definition nd_replicate
  : forall
    {Judgment}{Rule}{Ob}
    (h:Ob->Judgment)
    (c:Ob->Judgment)
    (j:Tree ??Ob),
    (forall (o:Ob), @ND Judgment Rule [h o] [c o]) ->
    @ND Judgment Rule (mapOptionTree h j) (mapOptionTree c j).
  intros.
  induction j; simpl.
    destruct a; simpl.
    apply X.
    apply nd_id0.
    apply nd_prod; auto.
    Defined.

(* "map" over natural deduction proofs, where the result proof has the same judgments (but different rules) *)
Definition nd_map
  : forall
    {Judgment}{Rule0}{Rule1}
    (r:forall h c, Rule0 h c -> @ND Judgment Rule1 h c)
    {h}{c}
    (pf:@ND Judgment Rule0 h c)
    ,
    @ND Judgment Rule1 h c.
    intros Judgment Rule0 Rule1 r.

    refine ((fix nd_map h c pf {struct pf} :=
     ((match pf
         in @ND _ _ H C
          return
          @ND Judgment Rule1 H C
        with
        | nd_id0                     => let case_nd_id0     := tt in _
        | nd_id1     h               => let case_nd_id1     := tt in _
        | nd_weak    h               => let case_nd_weak    := tt in _
        | nd_copy    h               => let case_nd_copy    := tt in _
        | nd_prod    _ _ _ _ lpf rpf => let case_nd_prod    := tt in _
        | nd_comp    _ _ _   top bot => let case_nd_comp    := tt in _
        | nd_rule    _ _     rule    => let case_nd_rule    := tt in _
        | nd_cancell _               => let case_nd_cancell := tt in _
        | nd_cancelr _               => let case_nd_cancelr := tt in _
        | nd_llecnac _               => let case_nd_llecnac := tt in _
        | nd_rlecnac _               => let case_nd_rlecnac := tt in _
        | nd_assoc   _ _ _           => let case_nd_assoc   := tt in _
        | nd_cossa   _ _ _           => let case_nd_cossa   := tt in _
      end))) ); simpl in *.

    destruct case_nd_id0.      apply nd_id0.
    destruct case_nd_id1.      apply nd_id1.
    destruct case_nd_weak.     apply nd_weak.
    destruct case_nd_copy.     apply nd_copy.
    destruct case_nd_prod.     apply (nd_prod (nd_map _ _ lpf) (nd_map _ _ rpf)).
    destruct case_nd_comp.     apply (nd_comp (nd_map _ _ top) (nd_map _ _ bot)).
    destruct case_nd_cancell.  apply nd_cancell.
    destruct case_nd_cancelr.  apply nd_cancelr.
    destruct case_nd_llecnac.  apply nd_llecnac.
    destruct case_nd_rlecnac.  apply nd_rlecnac.
    destruct case_nd_assoc.    apply nd_assoc.
    destruct case_nd_cossa.    apply nd_cossa.
    apply r. apply rule.
    Defined.

(* "map" over natural deduction proofs, where the result proof has different judgments *)
Definition nd_map'
  : forall
    {Judgment0}{Rule0}{Judgment1}{Rule1}
    (f:Judgment0->Judgment1)
    (r:forall h c, Rule0 h c -> @ND Judgment1 Rule1 (mapOptionTree f h) (mapOptionTree f c))
    {h}{c}
    (pf:@ND Judgment0 Rule0 h c)
    ,
    @ND Judgment1 Rule1 (mapOptionTree f h) (mapOptionTree f c).
    intros Judgment0 Rule0 Judgment1 Rule1 f r.
    
    refine ((fix nd_map' h c pf {struct pf} :=
     ((match pf
         in @ND _ _ H C
          return
          @ND Judgment1 Rule1 (mapOptionTree f H) (mapOptionTree f C)
        with
        | nd_id0                     => let case_nd_id0     := tt in _
        | nd_id1     h               => let case_nd_id1     := tt in _
        | nd_weak    h               => let case_nd_weak    := tt in _
        | nd_copy    h               => let case_nd_copy    := tt in _
        | nd_prod    _ _ _ _ lpf rpf => let case_nd_prod    := tt in _
        | nd_comp    _ _ _   top bot => let case_nd_comp    := tt in _
        | nd_rule    _ _     rule    => let case_nd_rule    := tt in _
        | nd_cancell _               => let case_nd_cancell := tt in _
        | nd_cancelr _               => let case_nd_cancelr := tt in _
        | nd_llecnac _               => let case_nd_llecnac := tt in _
        | nd_rlecnac _               => let case_nd_rlecnac := tt in _
        | nd_assoc   _ _ _           => let case_nd_assoc   := tt in _
        | nd_cossa   _ _ _           => let case_nd_cossa   := tt in _
      end))) ); simpl in *.

    destruct case_nd_id0.      apply nd_id0.
    destruct case_nd_id1.      apply nd_id1.
    destruct case_nd_weak.     apply nd_weak.
    destruct case_nd_copy.     apply nd_copy.
    destruct case_nd_prod.     apply (nd_prod (nd_map' _ _ lpf) (nd_map' _ _ rpf)).
    destruct case_nd_comp.     apply (nd_comp (nd_map' _ _ top) (nd_map' _ _ bot)).
    destruct case_nd_cancell.  apply nd_cancell.
    destruct case_nd_cancelr.  apply nd_cancelr.
    destruct case_nd_llecnac.  apply nd_llecnac.
    destruct case_nd_rlecnac.  apply nd_rlecnac.
    destruct case_nd_assoc.    apply nd_assoc.
    destruct case_nd_cossa.    apply nd_cossa.
    apply r. apply rule.
    Defined.

(* witnesses the fact that every Rule in a particular proof satisfies the given predicate *)
Inductive nd_property {Judgment}{Rule}(P:forall h c, @Rule h c -> Prop) : forall {h}{c}, @ND Judgment Rule h c -> Prop :=
  | nd_property_structural      : forall h c pf, Structural pf -> @nd_property _ _ P h c pf
  | nd_property_prod            : forall h0 c0 pf0 h1 c1 pf1,
    @nd_property _ _ P h0 c0 pf0 -> @nd_property _ _ P h1 c1 pf1 -> @nd_property _ _ P _ _ (nd_prod pf0 pf1)
  | nd_property_comp            : forall h0 c0 pf0  c1 pf1,
    @nd_property _ _ P h0 c0 pf0 -> @nd_property _ _ P c0 c1 pf1 -> @nd_property _ _ P _ _ (nd_comp pf0 pf1)
  | nd_property_rule            : forall h c r, P h c r -> @nd_property _ _ P h c (nd_rule r).
  Hint Constructors nd_property.

Close Scope pf_scope.
Close Scope nd_scope.
