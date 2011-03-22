(*********************************************************************************************************************************)
(* NaturalDeduction:                                                                                                             *)
(*                                                                                                                               *)
(*   Structurally explicit natural deduction proofs.                                                                             *)
(*                                                                                                                               *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.
Require Import ProductCategories_ch1_6_1.
Require Import OppositeCategories_ch1_6_2.
Require Import Enrichment_ch2_8.
Require Import Subcategories_ch7_1.
Require Import NaturalTransformations_ch7_4.
Require Import NaturalIsomorphisms_ch7_5.
Require Import MonoidalCategories_ch7_8.
Require Import Coherence_ch7_8.
Require Import Enrichment_ch2_8.
Require Import RepresentableStructure_ch7_2.
Require Import NaturalDeduction.


(*
 *  Everything in the rest of this section is just groundwork meant to
 *  build up to the definition of the AcceptableLanguage class, which
 *  appears at the end of the section.  References to "the instance"
 *  mean instances of that class.  Think of this section as being one
 *  big Class { ... } definition, except that we declare most of the
 *  stuff outside the curly brackets in order to take advantage of
 *  Coq's section mechanism.
 *)   
Section Acceptable_Language.

  (* Formalized Definition 4.1.1, production $\tau$ *)
  Context {T    : Type}.               (* types of the language *)

  Inductive Sequent := sequent : Tree ??T -> Tree ??T -> Sequent.
     Notation "cs |= ss" := (sequent cs ss) : al_scope.
     (* Because of term irrelevance we need only store the *erased* (def
      * 4.4) trees; for this reason there is no Coq type directly
      * corresponding to productions $e$ and $x$ of 4.1.1, and TreeOT can
      * be used for productions $\Gamma$ and $\Sigma$ *)

  (* to do: sequent calculus equals natural deduction over sequents, theorem equals sequent with null antecedent, *)

  Context {Rule : Tree ??Sequent -> Tree ??Sequent -> Type}.

  Notation "H /⋯⋯/ C" := (ND Rule H C) : al_scope.

  Open Scope pf_scope.
  Open Scope nd_scope.
  Open Scope al_scope.

  (* Formalized Definition 4.1
   *
   * Note that from this abstract interface, the terms (expressions)
   * in the proof are not accessible at all; they don't need to be --
   * so long as we have access to the equivalence relation upon
   * proof-conclusions.  Moreover, hiding the expressions actually
   * makes the encoding in CiC work out easier for two reasons:
   *
   *  1. Because the denotation function is provided a proof rather
   *     than a term, it is a total function (the denotation function is
   *     often undefined for ill-typed terms).
   *
   *  2. We can define arr_composition of proofs without having to know how
   *     to compose expressions.  The latter task is left up to the client
   *     function which extracts an expression from a completed proof.
   *  
   * This also means that we don't need an explicit proof obligation for 4.1.2.
   *)
  Class AcceptableLanguage :=

  (* Formalized Definition 4.1: denotational semantics equivalence relation on the conclusions of proofs *)
  { al_eqv                   : @ND_Relation Sequent Rule
                                     where "pf1 === pf2" := (@ndr_eqv _ _ al_eqv _ _ pf1 pf2)

  (* Formalized Definition 4.1.3; note that t here is either $\top$ or a single type, not a Tree of types;
   * we rely on "completeness of atomic initial segments" (http://en.wikipedia.org/wiki/Completeness_of_atomic_initial_sequents)
   * to generate the rest *)
  ; al_reflexive_seq         : forall t, Rule [] [t|=t]

  (* these can all be absorbed into a separate "sequent calculus" presentation *)
  ; al_ant_assoc     : forall {a b c d}, Rule [(a,,b),,c|=d]     [(a,,(b,,c))|=d]
  ; al_ant_cossa     : forall {a b c d}, Rule [a,,(b,,c)|=d]     [((a,,b),,c)|=d]
  ; al_ant_cancell   : forall {a b    }, Rule [  [],,a  |=b]     [        a  |=b]
  ; al_ant_cancelr   : forall {a b    }, Rule [a,,[]    |=b]     [        a  |=b]
  ; al_ant_llecnac   : forall {a b    }, Rule [      a  |=b]     [  [],,a    |=b]
  ; al_ant_rlecnac   : forall {a b    }, Rule [      a  |=b]     [  a,,[]    |=b]
  ; al_suc_assoc     : forall {a b c d}, Rule [d|=(a,,b),,c]     [d|=(a,,(b,,c))]
  ; al_suc_cossa     : forall {a b c d}, Rule [d|=a,,(b,,c)]     [d|=((a,,b),,c)]
  ; al_suc_cancell   : forall {a b    }, Rule [a|=[],,b    ]     [a|=      b    ]
  ; al_suc_cancelr   : forall {a b    }, Rule [a|=b,,[]    ]     [a|=      b    ]
  ; al_suc_llecnac   : forall {a b    }, Rule [a|=      b  ]     [a|=[],,b      ]
  ; al_suc_rlecnac   : forall {a b    }, Rule [a|=      b  ]     [a|=b,,[]      ]

  ; al_horiz_expand_left            : forall tau {Gamma Sigma}, Rule [        Gamma |=        Sigma ] [tau,,Gamma|=tau,,Sigma]
  ; al_horiz_expand_right           : forall tau {Gamma Sigma}, Rule [        Gamma |=        Sigma ] [Gamma,,tau|=Sigma,,tau]

  (* these are essentially one way of formalizing
   * "completeness of atomic initial segments" (http://en.wikipedia.org/wiki/Completeness_of_atomic_initial_sequents) *)
  ; al_horiz_expand_left_reflexive  : forall a b, [#al_reflexive_seq b#];;[#al_horiz_expand_left  a#]===[#al_reflexive_seq (a,,b)#]
  ; al_horiz_expand_right_reflexive : forall a b, [#al_reflexive_seq a#];;[#al_horiz_expand_right b#]===[#al_reflexive_seq (a,,b)#]
  ; al_horiz_expand_right_then_cancel : forall a,
    ((([#al_reflexive_seq (a,, [])#] ;; [#al_ant_cancelr#]);; [#al_suc_cancelr#]) === [#al_reflexive_seq a#])

  ; al_vert_expand_ant_left       : forall x `(pf:[a|=b]/⋯⋯/[c|=d]),  [x,,a   |=   b   ]/⋯⋯/[x,,c   |=   d   ]
  ; al_vert_expand_ant_right      : forall x `(pf:[a|=b]/⋯⋯/[c|=d]),  [   a,,x|=   b   ]/⋯⋯/[   c,,x|=   d   ]
  ; al_vert_expand_suc_left       : forall x `(pf:[a|=b]/⋯⋯/[c|=d]),  [   a   |=x,,b   ]/⋯⋯/[   c   |=x,,d   ]
  ; al_vert_expand_suc_right      : forall x `(pf:[a|=b]/⋯⋯/[c|=d]),  [   a   |=   b,,x]/⋯⋯/[   c   |=   d,,x]
  ; al_vert_expand_ant_l_respects : forall x a b c d (f g:[a|=b]/⋯⋯/[c|=d]),
      f===g -> al_vert_expand_ant_left x f === al_vert_expand_ant_left  x g
  ; al_vert_expand_ant_r_respects : forall x a b c d (f g:[a|=b]/⋯⋯/[c|=d]),
    f===g -> al_vert_expand_ant_right  x f === al_vert_expand_ant_right x g
  ; al_vert_expand_suc_l_respects : forall x a b c d (f g:[a|=b]/⋯⋯/[c|=d]),
    f===g -> al_vert_expand_suc_left   x f === al_vert_expand_suc_left  x g
  ; al_vert_expand_suc_r_respects : forall x a b c d (f g:[a|=b]/⋯⋯/[c|=d]),
    f===g -> al_vert_expand_suc_right  x f === al_vert_expand_suc_right x g
  ; al_vert_expand_ant_l_preserves_id : forall x a b, al_vert_expand_ant_left   x (nd_id [a|=b]) === nd_id [x,,a|=b]
  ; al_vert_expand_ant_r_preserves_id : forall x a b, al_vert_expand_ant_right  x (nd_id [a|=b]) === nd_id [a,,x|=b]
  ; al_vert_expand_suc_l_preserves_id : forall x a b, al_vert_expand_suc_left   x (nd_id [a|=b]) === nd_id [a|=x,,b]
  ; al_vert_expand_suc_r_preserves_id : forall x a b, al_vert_expand_suc_right  x (nd_id [a|=b]) === nd_id [a|=b,,x]
  ; al_vert_expand_ant_l_preserves_comp : forall x a b c d e f (h:[a|=b]/⋯⋯/[c|=d])(g:[c|=d]/⋯⋯/[e|=f]),
    (al_vert_expand_ant_left x (h;;g)) === (al_vert_expand_ant_left x h);;(al_vert_expand_ant_left x g)
  ; al_vert_expand_ant_r_preserves_comp : forall x a b c d e f (h:[a|=b]/⋯⋯/[c|=d])(g:[c|=d]/⋯⋯/[e|=f]),
    (al_vert_expand_ant_right x (h;;g)) === (al_vert_expand_ant_right x h);;(al_vert_expand_ant_right x g)
  ; al_vert_expand_suc_l_preserves_comp : forall x a b c d e f (h:[a|=b]/⋯⋯/[c|=d])(g:[c|=d]/⋯⋯/[e|=f]),
    (al_vert_expand_suc_left x (h;;g)) === (al_vert_expand_suc_left x h);;(al_vert_expand_suc_left x g)
  ; al_vert_expand_suc_r_preserves_comp : forall x a b c d e f (h:[a|=b]/⋯⋯/[c|=d])(g:[c|=d]/⋯⋯/[e|=f]),
    (al_vert_expand_suc_right x (h;;g)) === (al_vert_expand_suc_right x h);;(al_vert_expand_suc_right x g)

  ; al_subst                 : forall a b c,  [ a |= b ] ,, [ b |= c ] /⋯⋯/ [ a |= c ]
  ; al_subst_associativity : forall {a b c d},
      ((al_subst a b c) ** (nd_id1 (c|=d))) ;;
      (al_subst a c d)
      ===
      nd_assoc ;;
      ((nd_id1 (a|=b)) ** (al_subst b c d) ;;
      (al_subst a b d))
  ; al_subst_associativity' : forall {a b c d},
      nd_cossa ;;
      ((al_subst a b c) ** (nd_id1 (c|=d))) ;;
      (al_subst a c d)
      ===
      ((nd_id1 (a|=b)) ** (al_subst b c d) ;;
      (al_subst a b d))

  ; al_subst_left_identity  : forall `(pf:h/⋯⋯/[t1|=t2]), nd_llecnac;;((    [#al_reflexive_seq t1#]**pf);; al_subst _ _ _) === pf
  ; al_subst_right_identity : forall `(pf:h/⋯⋯/[t1|=t2]), nd_rlecnac;;((pf**[#al_reflexive_seq t2#]    );; al_subst _ _ _) === pf
  ; al_subst_commutes_with_horiz_expand_left : forall a b c d,
    [#al_horiz_expand_left d#] ** [#al_horiz_expand_left d#];; al_subst (d,, a) (d,, b) (d,, c)
    === al_subst a b c;; [#al_horiz_expand_left d#]
  ; al_subst_commutes_with_horiz_expand_right : forall a b c d,
    [#al_horiz_expand_right d#] ** [#al_horiz_expand_right d#] ;; al_subst (a,, d) (b,, d) (c,, d)
    === al_subst a b c;; [#al_horiz_expand_right d#]
  ; al_subst_commutes_with_vertical_expansion : forall t0 t1 t2, forall (f:[[]|=t1]/⋯⋯/[[]|=t0])(g:[[]|=t0]/⋯⋯/[[]|=t2]),
   (((nd_rlecnac;;
      ((([#al_reflexive_seq (t1,, [])#];; al_vert_expand_ant_left t1 (al_vert_expand_suc_right [] f));;
        (nd_rule al_ant_cancelr));; (nd_rule al_suc_cancelr)) ** nd_id0);;
     (nd_id [t1 |= t0]) **
     ((([#al_reflexive_seq (t0,, [])#];; al_vert_expand_ant_left t0 (al_vert_expand_suc_right [] g));;
       (nd_rule al_ant_cancelr));; (nd_rule al_suc_cancelr)));; 
    al_subst t1 t0 t2)
   ===
    ((([#al_reflexive_seq (t1,, [])#];;
          (al_vert_expand_ant_left t1 (al_vert_expand_suc_right [] f);;
           al_vert_expand_ant_left t1 (al_vert_expand_suc_right [] g)));; 
         (nd_rule al_ant_cancelr));; (nd_rule al_suc_cancelr))
  }.

  Notation "pf1 === pf2" := (@ndr_eqv _ _ al_eqv _ _ pf1 pf2) : temporary_scope3.
  Open Scope temporary_scope3.

  Lemma al_subst_respects :
    forall {AL:AcceptableLanguage}{a b c},
      forall
      (f  : [] /⋯⋯/ [a |= b])
      (f' : [] /⋯⋯/ [a |= b])
      (g  : [] /⋯⋯/ [b |= c])
      (g' : [] /⋯⋯/ [b |= c]),
      (f === f') ->
      (g === g') ->
      (f ** g;; al_subst _ _ _) === (f' ** g';; al_subst _ _ _).
    intros.
    setoid_rewrite H.
    setoid_rewrite H0.
    reflexivity.
    Defined.

  (* a contextually closed language *)
  (*
  Class ContextuallyClosedAcceptableLanguage :=
  { ccal_al                          :  AcceptableLanguage
  ; ccal_contextual_closure_operator :  Tree ??T -> Tree ??T -> Tree ??T
  where "a -~- b" := (ccal_contextual_closure_operator a b)
  ; ccal_contextual_closure          :  forall {a b c d}(f:[a|=b]/⋯⋯/[c|=d]),     [[]|=a-~-b]/⋯⋯/[[]|=c-~-d]
  ; ccal_contextual_closure_respects :  forall {a b c d}(f f':[a|=b]/⋯⋯/[c|=d]),
                                                  f===f' -> (ccal_contextual_closure f)===(ccal_contextual_closure f')
  ; ccal_contextual_closure_preserves_comp :  forall {a b c d e f}(f':[a|=b]/⋯⋯/[c|=d])(g':[c|=d]/⋯⋯/[e|=f]),
             (ccal_contextual_closure f');;(ccal_contextual_closure g') === (ccal_contextual_closure (f';;g'))
  ; ccal_contextual_closure_preserves_id :  forall {a b}, ccal_contextual_closure (nd_id [a|=b]) === nd_id [[]|=a-~-b]
  }.
  Coercion ccal_al : ContextuallyClosedAcceptableLanguage >-> AcceptableLanguage.
  *)

  (* languages with unrestricted substructural rules (like that of Section 5) additionally implement this class *)
  Class AcceptableLanguageWithUnrestrictedSubstructuralRules :=
  { alwusr_al :> AcceptableLanguage
  ; al_contr  : forall a b,     Rule [a,,a |= b ]  [    a |= b]
  ; al_exch   : forall a b c,   Rule [a,,b |= c ]  [(b,,a)|= c]
  ; al_weak   : forall a b,     Rule [[] |= b ]  [    a |= b]
  }.
  Coercion alwusr_al : AcceptableLanguageWithUnrestrictedSubstructuralRules >-> AcceptableLanguage.

  (* languages with a fixpoint operator *)
  Class AcceptableLanguageWithFixpointOperator `(al:AcceptableLanguage) :=
  { alwfpo_al := al
  ; al_fix    : forall a b x,   Rule [a,,x |= b,,x]  [a |= b]
  }.
  Coercion alwfpo_al : AcceptableLanguageWithFixpointOperator >-> AcceptableLanguage.

  Close Scope temporary_scope3.
  Close Scope al_scope.
  Close Scope nd_scope.
  Close Scope pf_scope.

End Acceptable_Language.

Implicit Arguments ND [ Judgment ].

Open Scope nd_scope.
  Add Parametric Morphism {T Rule AL a b c d e} : (@al_vert_expand_suc_right T Rule AL a b c d e)
  with signature ((ndr_eqv(ND_Relation:=al_eqv)) ==> (ndr_eqv(ND_Relation:=al_eqv)))
    as parametric_morphism_al_vert_expand_suc_right.
    intros; apply al_vert_expand_suc_r_respects; auto.
    Defined.
  Add Parametric Morphism {T Rule AL a b c d e} : (@al_vert_expand_suc_left T Rule AL a b c d e)
  with signature ((ndr_eqv(ND_Relation:=al_eqv)) ==> (ndr_eqv(ND_Relation:=al_eqv)))
    as parametric_morphism_al_vert_expand_suc_left.
    intros; apply al_vert_expand_suc_l_respects; auto.
    Defined.
  Add Parametric Morphism {T Rule AL a b c d e} : (@al_vert_expand_ant_right T Rule AL a b c d e)
  with signature ((ndr_eqv(ND_Relation:=al_eqv)) ==> (ndr_eqv(ND_Relation:=al_eqv)))
    as parametric_morphism_al_vert_expand_ant_right.
    intros; apply al_vert_expand_ant_r_respects; auto.
    Defined.
  Add Parametric Morphism {T Rule AL a b c d e} : (@al_vert_expand_ant_left T Rule AL a b c d e)
  with signature ((ndr_eqv(ND_Relation:=al_eqv)) ==> (ndr_eqv(ND_Relation:=al_eqv)))
    as parametric_morphism_al_vert_expand_ant_left.
    intros; apply al_vert_expand_ant_l_respects; auto.
    Defined.
Close Scope nd_scope.

Notation "cs |= ss" := (@sequent _ cs ss) : al_scope.
(*
Definition mapSequent {T R:Type}(f:Tree ??T -> Tree ??R)(seq:@Sequent T) : @Sequent R :=
  match seq with sequentpair a b => pair (f a) (f b) end.
Implicit Arguments Sequent [ ].
*)


(* proofs which are generic and apply to any acceptable langauge (most of section 4) *)
Section Acceptable_Language_Facts.

  (* the ambient language about which we are proving facts *)
  Context `(Lang : @AcceptableLanguage T Rule).

  (* just for this section *)
  Open Scope nd_scope.
  Open Scope al_scope.
  Open Scope pf_scope.
  Notation "H /⋯⋯/ C" := (@ND Sequent Rule H C)     : temporary_scope4.
  Notation "a === b"  := (@ndr_eqv _ _ al_eqv _ _ a b)                   : temporary_scope4.
  Open Scope temporary_scope4.

  Definition lang_al_eqv := al_eqv(AcceptableLanguage:=Lang).
  Existing Instance lang_al_eqv.

  Ltac distribute :=
    match goal with
     [ |- ?G ] =>
      match G with
        context ct [(?A ** ?B) ;; (?C ** ?D)] => 
           setoid_rewrite <- (ndr_prod_preserves_comp A B C D)
      end
      end.

  Ltac sequentialize_product A B :=
    match goal with
     [ |- ?G ] =>
      match G with
      | context ct [(A ** B)] =>
          setoid_replace (A ** B)
        with ((A ** (nd_id _)) ;; ((nd_id _) ** B))
        (*with ((A ** (nd_id _)) ;; ((nd_id _) ** B))*)
    end end.
  Ltac sequentialize_product' A B :=
    match goal with
     [ |- ?G ] =>
      match G with
      | context ct [(A ** B)] =>
          setoid_replace (A ** B)
        with (((nd_id _) ** B) ;; (A ** (nd_id _)))
        (*with ((A ** (nd_id _)) ;; ((nd_id _) ** B))*)
    end end.
  Ltac distribute' :=
    match goal with
     [ |- ?G ] =>
      match G with
        context ct [(?A ;; ?B) ** (?C ;; ?D)] => 
           setoid_rewrite (ndr_prod_preserves_comp A B C D)
      end
      end.
  Ltac distribute_left_product_with_id :=
    match goal with
     [ |- ?G ] =>
      match G with
        context ct [(nd_id ?A) ** (?C ;; ?D)] => 
           setoid_replace ((nd_id A) ** (C ;; D)) with ((nd_id A ;; nd_id A) ** (C ;; D));
        [ setoid_rewrite (ndr_prod_preserves_comp (nd_id A) C (nd_id A) D) | idtac ]
      end
      end.
  Ltac distribute_right_product_with_id :=
    match goal with
     [ |- ?G ] =>
      match G with
        context ct [(?C ;; ?D) ** (nd_id ?A)] => 
           setoid_replace ((C ;; D) ** (nd_id A)) with ((C ;; D) ** (nd_id A ;; nd_id A));
        [ setoid_rewrite (ndr_prod_preserves_comp C (nd_id A) D (nd_id A)) | idtac ]
      end
      end.

  (* another phrasing of al_subst_associativity; obligations tend to show up in this form *)
  Lemma al_subst_associativity'' : 
    forall (a b : T) (f : [] /⋯⋯/ [[a] |= [b]]) (c : T) (g : [] /⋯⋯/ [[b] |= [c]]) 
    (d : T) (h : [] /⋯⋯/ [[c] |= [d]]),
    nd_llecnac;; ((nd_llecnac;; (f ** g;; al_subst [a] [b] [c])) ** h;; al_subst [a] [c] [d]) ===
    nd_llecnac;; (f ** (nd_llecnac;; (g ** h;; al_subst [b] [c] [d]));; al_subst [a] [b] [d]).
    intros.
      sequentialize_product' (nd_llecnac;; (f ** g;; al_subst [a] [b] [c])) h.
      repeat setoid_rewrite <- ndr_comp_associativity.
      distribute_right_product_with_id.
      repeat setoid_rewrite ndr_comp_associativity.
      set (@al_subst_associativity) as q. setoid_rewrite q. clear q.
      apply ndr_comp_respects; try reflexivity.
      repeat setoid_rewrite <- ndr_comp_associativity.
      apply ndr_comp_respects; try reflexivity.
      sequentialize_product f ((nd_llecnac;; g ** h);; al_subst [b] [c] [d]).
      distribute_left_product_with_id.
      repeat setoid_rewrite <- ndr_comp_associativity.
      apply ndr_comp_respects; try reflexivity.
      setoid_rewrite <- ndr_prod_preserves_comp.
      repeat setoid_rewrite ndr_comp_left_identity.
      repeat setoid_rewrite ndr_comp_right_identity.
    admit.
    admit.
    admit.
    admit.
    admit.
    Qed.

  (* Formalized Definition 4.6 *)
  Section Types1.
    Instance Types1 : Category T (fun t1 t2 => [ ] /⋯⋯/ [ [t1] |= [t2] ]) :=
    { eqv  := fun ta tb pf1 pf2                                            => pf1 === pf2
    ; id   := fun t                                                        => [#al_reflexive_seq [t]#]
    ; comp := fun {ta tb tc:T}(pf1:[]/⋯⋯/[[ta]|=[tb]])(pf2:[]/⋯⋯/[[tb]|=[tc]]) => nd_llecnac ;; ((pf1 ** pf2) ;; (al_subst _ _ _))
    }.
    intros; apply Build_Equivalence;
      [ unfold Reflexive; intros; reflexivity
      | unfold Symmetric; intros; symmetry; auto
      | unfold Transitive; intros; transitivity y; auto ].
    unfold Proper; unfold respectful; intros; simpl.
      apply ndr_comp_respects. reflexivity.
      apply al_subst_respects; auto.
    intros; simpl. apply al_subst_left_identity.
    intros; simpl.
      assert (@nd_llecnac _ Rule [] === @nd_rlecnac _ _ []).
      apply ndr_structural_indistinguishable; auto.
      setoid_rewrite H.
      apply al_subst_right_identity.
    intros; apply al_subst_associativity''.
    Defined.
  End Types1.

  (* Formalized Definition 4.10 *)
  Instance Judgments : Category (Tree ??Sequent) (fun h c => h /⋯⋯/ c) :=
  { id   := fun h          => nd_id _
  ; comp := fun a b c f g  => f ;; g
  ; eqv  := fun a b f g    => f===g
  }.
  intros; apply Build_Equivalence;
    [ unfold Reflexive; intros; reflexivity
    | unfold Symmetric; intros; symmetry; auto
    | unfold Transitive; intros; transitivity y; auto ].
  unfold Proper; unfold respectful; intros; simpl; apply ndr_comp_respects; auto.
  intros; apply ndr_comp_left_identity.
  intros; apply ndr_comp_right_identity.
  intros; apply ndr_comp_associativity.
  Defined.

  (* a "primitive" proof has exactly one hypothesis and one conclusion *)
  Inductive IsPrimitive : forall (h_:Tree ??(@Sequent T)), Type :=
    isPrimitive : forall h, IsPrimitive [h].
  Hint Constructors IsPrimitive.
  Instance IsPrimitiveSubCategory : SubCategory Judgments IsPrimitive (fun _ _ _ _ _ => True).
    apply Build_SubCategory; intros; auto.
    Defined.

  (* The primitive judgments form a subcategory; nearly all of the
   * functors we build that go into Judgments will factor through the
   * inclusion functor for this subcategory.  Explicitly constructing
   * it makes the formalization easier, but distracts from what's
   * actually going on (from an expository perspective) *)
  Definition PrimitiveJudgments := SubCategoriesAreCategories Judgments IsPrimitiveSubCategory.
  Definition PrimitiveInclusion := InclusionFunctor           Judgments IsPrimitiveSubCategory.

  Section Types0.
    Inductive IsNil    : Tree ??(@Sequent T) -> Prop := isnil    : IsNil [].
    Inductive IsClosed : Tree ??(@Sequent T) -> Prop := isclosed:forall t, IsClosed [[]|=[t]].
    Inductive IsIdentity : forall h c,  (h /⋯⋯/ c) -> Prop :=
      | isidentity0 : forall t,         IsIdentity t t (nd_id t)
      | isidentity1 : forall t pf1 pf2, IsIdentity t t pf1 -> IsIdentity t t pf2 -> IsIdentity t t (pf1 ;; pf2).
    Inductive IsInTypes0  (h c:Tree ??Sequent)(pf:h /⋯⋯/ c) : Prop :=
      | iit0_id0   : IsNil h    -> IsNil    c -> IsIdentity _ _ pf -> IsInTypes0 _ _ pf
      | iit0_id1   : @IsClosed  h -> @IsClosed   c -> IsIdentity _ _ pf -> IsInTypes0 _ _ pf
      | iit0_term  : IsNil h    -> @IsClosed c ->                      IsInTypes0 _ _ pf.
     Instance Types0P : SubCategory Judgments
        (fun x:Judgments => IsInTypes0 _ _ (id(Category:=Judgments) x))
        (fun h c _ _ f => IsInTypes0 h c f).
     intros.
       apply Build_SubCategory; intros; simpl.
        auto.
        inversion H0.
          inversion H1; subst.
          inversion H2; subst.
          inversion H; subst. inversion H4; subst.
          apply iit0_id0; auto. apply isidentity1; auto.
          inversion H5.
          inversion H5.
          inversion H1; subst.
          inversion H2; subst.
          inversion H3; subst. clear H8. clear H7.
            inversion H; subst. inversion H5.
            inversion H4; subst.
            inversion H6; subst.
            apply iit0_id1; auto. apply isidentity1; auto.
            clear H10. clear H8.
            apply iit0_id1; auto. apply isidentity1; auto.
            inversion H4; subst. inversion H; subst.
            inversion H8.
            inversion H6.
            apply iit0_term; auto.
        clear H7; subst.
          inversion H; subst.
          inversion H4; subst.
          apply iit0_term; auto.
          inversion H4; subst.
            inversion H7; subst. clear H14.
            apply iit0_id1; auto. apply isidentity1; auto.
            clear H13.
            apply iit0_id1; auto. apply isidentity1; auto.
            inversion H4; subst.
            inversion H; subst.
            inversion H10.
            inversion H7.
            apply iit0_term; auto.
        inversion H1; subst.
        inversion H; subst.
          inversion H3; subst. apply iit0_term; auto.
          inversion H4.
          inversion H4.
       Qed.
    
    (* Formalized Definition 4.8 *)
    Definition Types0 := SubCategoriesAreCategories Judgments Types0P.
  End Types0.

  (* Formalized Definition 4.11 *)
  Instance Judgments_binoidal : BinoidalCat Judgments (fun a b:Tree ??Sequent => a,,b) :=
  { bin_first  := fun x => @Build_Functor _ _ Judgments _ _ Judgments (fun a => a,,x)   (fun a b (f:a/⋯⋯/b) => f**(nd_id x)) _ _ _
  ; bin_second := fun x => @Build_Functor _ _ Judgments _ _ Judgments (fun a => x,,a)   (fun a b (f:a/⋯⋯/b) => (nd_id x)**f) _ _ _
  }.
    intros. simpl. simpl in H. setoid_rewrite H. reflexivity.
    intros. simpl. reflexivity.
    intros. simpl. setoid_rewrite <- ndr_prod_preserves_comp. setoid_rewrite ndr_comp_left_identity. reflexivity.
    intros. simpl. simpl in H. setoid_rewrite H. reflexivity.
    intros. simpl. reflexivity.
    intros. simpl. setoid_rewrite <- ndr_prod_preserves_comp. setoid_rewrite ndr_comp_left_identity. reflexivity.
    Defined.

  Definition jud_assoc_iso (a b c:Judgments) : @Isomorphic _ _ Judgments ((a,,b),,c) (a,,(b,,c)).
    apply (@Build_Isomorphic _ _ Judgments _ _ nd_assoc nd_cossa); simpl; auto.
    Defined.
  Definition jud_cancelr_iso (a:Judgments) : @Isomorphic _ _ Judgments (a,,[]) a.
    apply (@Build_Isomorphic _ _ Judgments _ _ nd_cancelr nd_rlecnac); simpl; auto.
    Defined.
  Definition jud_cancell_iso (a:Judgments) : @Isomorphic _ _ Judgments ([],,a) a.
    apply (@Build_Isomorphic _ _ Judgments _ _ nd_cancell nd_llecnac); simpl; auto.
    Defined.

  (* just for this section *)
  Notation "a ⊗ b"  := (@bin_obj    _ _ Judgments _ Judgments_binoidal a b).
  Notation "c ⋊ -"  := (@bin_second _ _ Judgments _ Judgments_binoidal c).
  Notation "- ⋉ c"  := (@bin_first  _ _ Judgments _ Judgments_binoidal c).
  Notation "c ⋊ f"  := ((c ⋊ -) \ f).
  Notation "g ⋉ c"  := ((- ⋉ c) \ g).

  Hint Extern 1 => apply (@nd_structural_id0 _ Rule).
  Hint Extern 1 => apply (@nd_structural_id1 _ Rule).
  Hint Extern 1 => apply (@nd_structural_weak _ Rule).
  Hint Extern 1 => apply (@nd_structural_copy _ Rule).
  Hint Extern 1 => apply (@nd_structural_prod _ Rule).
  Hint Extern 1 => apply (@nd_structural_comp _ Rule).
  Hint Extern 1 => apply (@nd_structural_cancell _ Rule).
  Hint Extern 1 => apply (@nd_structural_cancelr _ Rule).
  Hint Extern 1 => apply (@nd_structural_llecnac _ Rule).
  Hint Extern 1 => apply (@nd_structural_rlecnac _ Rule).
  Hint Extern 1 => apply (@nd_structural_assoc _ Rule).
  Hint Extern 1 => apply (@nd_structural_cossa _ Rule).
  Hint Extern 2 => apply (@ndr_structural_indistinguishable _ Rule).

  Program Instance Judgments_premonoidal  : PreMonoidalCat Judgments_binoidal [ ] :=
  { pmon_assoc     := fun a b => @Build_NaturalIsomorphism _ _ _ _ _ _ _ _ _ _ (fun x => (jud_assoc_iso a x b))   _
  ; pmon_cancell   :=            @Build_NaturalIsomorphism _ _ _ _ _ _ _ _ _ _ (fun x => (jud_cancell_iso x))     _
  ; pmon_cancelr   :=            @Build_NaturalIsomorphism _ _ _ _ _ _ _ _ _ _ (fun x => (jud_cancelr_iso x))     _
  ; pmon_assoc_rr  := fun a b => @Build_NaturalIsomorphism _ _ _ _ _ _ _ _ _ _ (fun x => (jud_assoc_iso x a b)⁻¹) _
  ; pmon_assoc_ll  := fun a b => @Build_NaturalIsomorphism _ _ _ _ _ _ _ _ _ _ (fun x => jud_assoc_iso a b x)     _
  }.
  Next Obligation.
    setoid_rewrite (ndr_prod_associativity (nd_id a) f (nd_id b)).
    repeat setoid_rewrite ndr_comp_associativity.
    apply ndr_comp_respects; try reflexivity.
    symmetry.
    eapply transitivity; [ idtac | apply ndr_comp_right_identity ].
    apply ndr_comp_respects; try reflexivity; simpl; auto.
    Defined.
  Next Obligation.
    setoid_rewrite (ndr_prod_right_identity f).
    repeat setoid_rewrite ndr_comp_associativity.
    apply ndr_comp_respects; try reflexivity.
    symmetry.
    eapply transitivity; [ idtac | apply ndr_comp_right_identity ].
    apply ndr_comp_respects; try reflexivity; simpl; auto.
    Defined.
  Next Obligation.
    setoid_rewrite (ndr_prod_left_identity f).
    repeat setoid_rewrite ndr_comp_associativity.
    apply ndr_comp_respects; try reflexivity.
    symmetry.
    eapply transitivity; [ idtac | apply ndr_comp_right_identity ].
    apply ndr_comp_respects; try reflexivity; simpl; auto.
    Defined.
  Next Obligation.
    apply Build_Pentagon; intros.
    simpl; apply ndr_structural_indistinguishable; auto.
    Defined.
  Next Obligation.
    apply Build_Triangle; intros;
    simpl; apply ndr_structural_indistinguishable; auto.
    Defined.
  Next Obligation.
    setoid_rewrite (ndr_prod_associativity f (nd_id a) (nd_id b)).
    repeat setoid_rewrite <- ndr_comp_associativity.
    apply ndr_comp_respects; try reflexivity.
    eapply transitivity; [ idtac | apply ndr_comp_left_identity ].
    apply ndr_comp_respects; try reflexivity; simpl; auto.
    Defined.
  Next Obligation.
    setoid_rewrite (ndr_prod_associativity (nd_id a) (nd_id b) f).
    repeat setoid_rewrite ndr_comp_associativity.
    apply ndr_comp_respects; try reflexivity.
    symmetry.
    eapply transitivity; [ idtac | apply ndr_comp_right_identity ].
    apply ndr_comp_respects; try reflexivity; simpl; auto.
    Defined.
    Check (@Judgments_premonoidal).  (* to force Coq to verify that we've finished all the obligations *)

  Definition Judgments_monoidal_endofunctor_fobj : Judgments ×× Judgments -> Judgments :=
    (fun xy =>
     match xy with
     | pair_obj x y => T_Branch x y
     end).
  Definition Judgments_monoidal_endofunctor_fmor :
           forall a b, (a~~{Judgments ×× Judgments}~~>b) ->
           ((Judgments_monoidal_endofunctor_fobj a)~~{Judgments}~~>(Judgments_monoidal_endofunctor_fobj b)).
     intros.
     destruct a.
     destruct b.
     destruct X.
     exact (h**h0).
     Defined.
  Definition Judgments_monoidal_endofunctor : Functor (Judgments ×× Judgments) Judgments Judgments_monoidal_endofunctor_fobj.
    refine {| fmor := Judgments_monoidal_endofunctor_fmor |}; intros; simpl.
    abstract (destruct a; destruct b; destruct f; destruct f'; auto; destruct H; apply ndr_prod_respects; auto).
    abstract (destruct a; simpl; reflexivity).
    abstract (destruct a; destruct b; destruct c; destruct f; destruct g; symmetry; apply ndr_prod_preserves_comp).
    Defined.

  Instance Judgments_monoidal  : MonoidalCat _ _ Judgments_monoidal_endofunctor [ ].
    admit.
    Defined.

  (* all morphisms in the category of Judgments are central; there's probably a very short route from here to CartesianCat *)
  Lemma all_central : forall a b:Judgments, forall (f:a~>b), CentralMorphism f.
    intros; apply Build_CentralMorphism; intros.
    simpl.
      setoid_rewrite <- (ndr_prod_preserves_comp f (nd_id _) (nd_id _) g).
      setoid_rewrite <- (ndr_prod_preserves_comp (nd_id _) g f (nd_id _)).
      setoid_rewrite ndr_comp_left_identity.
      setoid_rewrite ndr_comp_right_identity.
      reflexivity.
    simpl.
      setoid_rewrite <- (ndr_prod_preserves_comp g (nd_id _) (nd_id _) f).
      setoid_rewrite <- (ndr_prod_preserves_comp (nd_id _) f g (nd_id _)).
      setoid_rewrite ndr_comp_left_identity.
      setoid_rewrite ndr_comp_right_identity.
      reflexivity.
    Defined.

  (*
  Instance NoHigherOrderFunctionTypes : SubCategory Judgments
  Instance            NoFunctionTypes : SubCategory Judgments
  Lemma first_order_functions_eliminable : IsomorphicCategories NoHigherOrderFunctionTypes NoFunctionTypes
  *)

  (* Formalized Theorem 4.19 *)
  Instance Types_omega_e : ECategory Judgments_monoidal (Tree ??T) (fun tt1 tt2 => [ tt1 |= tt2 ]) :=
  { eid             := fun tt      => [#al_reflexive_seq tt#]
  ; ecomp           := fun a b c   => al_subst a b c
  }.
    admit.
    admit.
    admit.
    admit.
    admit.
    Defined.

  Definition Types_omega_monoidal_functor
    : Functor (Types_omega_e ×× Types_omega_e) Types_omega_e (fun a => match a with pair_obj a1 a2 => a1,,a2 end).
    admit.
    Defined.

  Instance Types_omega_monoidal : MonoidalCat Types_omega_e _ Types_omega_monoidal_functor [].
    admit.
    Defined.

  Definition AL_Enrichment : Enrichment.
    refine {| enr_c   := Types_omega_e |}.
    Defined.

  Definition AL_SurjectiveEnrichment : SurjectiveEnrichment.
    refine {| se_enr  := AL_Enrichment |}.
    unfold treeDecomposition.
    intros; induction d; simpl.
    destruct a.
    destruct s.
    exists [pair t t0]; auto.
    exists []; auto.
    destruct IHd1.
    destruct IHd2.
    exists (x,,x0); subst; auto.
    Defined.

  Definition AL_MonoidalEnrichment : MonoidalEnrichment.
    refine {| me_enr := AL_SurjectiveEnrichment ; me_mon := Types_omega_monoidal |}.
    admit.
    Defined.

  Definition AL_MonicMonoidalEnrichment : MonicMonoidalEnrichment.
    refine {| ffme_enr := AL_MonoidalEnrichment |}.
    admit.
    admit.
    admit.
    Defined.

  (*
  Instance Types_omega_be : BinoidalECategory Types_omega_e :=
  { bec_obj     := fun tt1 tt2 => tt1,,tt2
  ; bec_efirst  := fun a b c   => nd_rule (@al_horiz_expand_right _ _ Lang _ _ _)
  ; bec_esecond := fun a b c   => nd_rule (@al_horiz_expand_left  _ _ Lang _ _ _)
  }.
    intros; apply all_central.
    intros; apply all_central.
    intros. unfold eid. simpl.
      setoid_rewrite <- al_horiz_expand_right_reflexive.
      reflexivity.
    intros. unfold eid. simpl.
      setoid_rewrite <- al_horiz_expand_left_reflexive.
      reflexivity.
    intros. simpl.
      set (@al_subst_commutes_with_horiz_expand_right _ _ _ a b c d) as q.
      setoid_rewrite <- q. clear q.
      apply ndr_comp_respects; try reflexivity.
      distribute.
      apply ndr_prod_respects.
      eapply transitivity; [ idtac | apply ndr_comp_right_identity ].
      apply ndr_comp_respects; reflexivity.
      eapply transitivity; [ idtac | apply ndr_comp_left_identity ].
      apply ndr_comp_respects; reflexivity.
    intros. simpl.
      set (@al_subst_commutes_with_horiz_expand_left _ _ _ a b c d) as q.
      setoid_rewrite <- q. clear q.
      apply ndr_comp_respects; try reflexivity.
      distribute.
      apply ndr_prod_respects.
      eapply transitivity; [ idtac | apply ndr_comp_right_identity ].
      apply ndr_comp_respects; reflexivity.
      eapply transitivity; [ idtac | apply ndr_comp_left_identity ].
      apply ndr_comp_respects; reflexivity.
      Defined.
  *)

  Definition Types_omega : Category _ (fun tt1 tt2 => [ ]/⋯⋯/[ tt1 |= tt2 ]) := Underlying Types_omega_e.
  Existing Instance Types_omega.

  (*
  Definition Types_omega_binoidal : BinoidalCat Types_omega (fun tt1 tt2 => tt1,,tt2) := Underlying_binoidal Types_omega_be.
  Existing Instance Types_omega_binoidal.
  *)

  (* takes an "operation in the context" (proof from [b|=Top]/⋯⋯/[a|=Top]) and turns it into a function a-->b; note the variance *)
  Definition context_operation_as_function
    : forall {a}{b} (f:[b|=[]]~~{Judgments}~~>[a|=[]]), []~~{Judgments}~~>[a|=b].
    intros.
    apply (@al_vert_expand_suc_right _ _ _ b _ _) in f.
    simpl in f.
    apply (@al_vert_expand_ant_left  _ _ _ [] _ _) in f.
    simpl in f.
    set ([#al_reflexive_seq _#] ;; f ;; [#al_ant_cancell#] ;; [#al_suc_cancell#]) as f'.
    exact f'.
    Defined.

  (* takes an "operation in the context" (proof from [Top|=a]/⋯⋯/[Top|=b]) and turns it into a function a-->b; note the variance *)
  Definition cocontext_operation_as_function
    : forall {a}{b} (f:[[]|=a]~~{Judgments}~~>[[]|=b]), []~~{Judgments}~~>[a|=b].
    intros. unfold hom. unfold hom in f.
    apply al_vert_expand_ant_right with (x:=a) in f.
    simpl in f.
    apply al_vert_expand_suc_left with (x:=[]) in f.
    simpl in f.
    set ([#al_reflexive_seq _#] ;; f ;; [#al_ant_cancell#] ;; [#al_suc_cancell#]) as f'.
    exact f'.
    Defined.


  Definition function_as_context_operation
    : forall {a}{b}{c} (f:[]~~{Judgments}~~>[a|=b]), [b|=c]~~{Judgments}~~>[a|=c]
    := fun a b c f => RepresentableFunctorºᑭ Types_omega_e c \ f.
  Definition function_as_cocontext_operation
    : forall {a}{b}{c} (f:[]/⋯⋯/[a|=b]), [c|=a]~~{Judgments}~~>[c|=b]
    := fun a b c f => RepresentableFunctor Types_omega_e c \ f.

  Close Scope temporary_scope4.
  Close Scope al_scope.
  Close Scope nd_scope.
  Close Scope pf_scope.
  Close Scope isomorphism_scope.
End Acceptable_Language_Facts.

Coercion AL_SurjectiveEnrichment    : AcceptableLanguage >-> SurjectiveEnrichment.
Coercion AL_MonicMonoidalEnrichment : AcceptableLanguage >-> MonicMonoidalEnrichment.
