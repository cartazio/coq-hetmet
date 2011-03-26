(*********************************************************************************************************************************)
(* ProgrammingLanguage                                                                                                           *)
(*                                                                                                                               *)
(*   Basic assumptions about programming languages .                                                                             *)
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
Require Import NaturalDeductionCategory.
Require Import Reification.
Require Import FreydCategories.
Require Import InitialTerminal_ch2_2.
Require Import FunctorCategories_ch7_7.
Require Import GeneralizedArrowFromReification.
Require Import GeneralizedArrow.


(*
 *  Everything in the rest of this section is just groundwork meant to
 *  build up to the definition of the ProgrammingLanguage class, which
 *  appears at the end of the section.  References to "the instance"
 *  mean instances of that class.  Think of this section as being one
 *  big Class { ... } definition, except that we declare most of the
 *  stuff outside the curly brackets in order to take advantage of
 *  Coq's section mechanism.
 *)   
Section Programming_Language.

  (* Formalized Definition 4.1.1, production $\tau$ *)
  Context {T    : Type}.               (* types of the language *)

  Context (Judg : Type).
  Context (sequent : Tree ??T -> Tree ??T -> Judg).
     Notation "cs |= ss" := (sequent cs ss) : al_scope.
     (* Because of term irrelevance we need only store the *erased* (def
      * 4.4) trees; for this reason there is no Coq type directly
      * corresponding to productions $e$ and $x$ of 4.1.1, and TreeOT can
      * be used for productions $\Gamma$ and $\Sigma$ *)

  (* to do: sequent calculus equals natural deduction over sequents, theorem equals sequent with null antecedent, *)

  Context {Rule : Tree ??Judg -> Tree ??Judg -> Type}.

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
  Class ProgrammingLanguage :=

  (* Formalized Definition 4.1: denotational semantics equivalence relation on the conclusions of proofs *)
  { al_eqv                   : @ND_Relation Judg Rule
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

  ; al_subst_left_identity  : forall a b, ((    [#al_reflexive_seq a#]**(nd_id _));; al_subst _ _ b) === nd_cancell
  ; al_subst_right_identity : forall a b, (((nd_id _)**[#al_reflexive_seq a#]    );; al_subst b _ _) === nd_cancelr
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

  Lemma al_subst_respects {PL:ProgrammingLanguage} :
    forall {a b c},
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

  (* languages with unrestricted substructural rules (like that of Section 5) additionally implement this class *)
  Class ProgrammingLanguageWithUnrestrictedSubstructuralRules :=
  { alwusr_al :> ProgrammingLanguage
  ; al_contr  : forall a b,     Rule [a,,a |= b ]  [    a |= b]
  ; al_exch   : forall a b c,   Rule [a,,b |= c ]  [(b,,a)|= c]
  ; al_weak   : forall a b,     Rule [[] |= b ]  [    a |= b]
  }.
  Coercion alwusr_al : ProgrammingLanguageWithUnrestrictedSubstructuralRules >-> ProgrammingLanguage.

  (* languages with a fixpoint operator *)
  Class ProgrammingLanguageWithFixpointOperator `(al:ProgrammingLanguage) :=
  { alwfpo_al := al
  ; al_fix    : forall a b x,   Rule [a,,x |= b,,x]  [a |= b]
  }.
  Coercion alwfpo_al : ProgrammingLanguageWithFixpointOperator >-> ProgrammingLanguage.

  Section LanguageCategory.

    Context (PL:ProgrammingLanguage).

    (* category of judgments in a fixed type/coercion context *)
    Definition JudgmentsL :=@Judgments_Category_monoidal _ Rule al_eqv.

    Definition identityProof t : [] ~~{JudgmentsL}~~> [t |= t].
      unfold hom; simpl.
      apply nd_rule.
      apply al_reflexive_seq.
      Defined.

    Definition cutProof a b c : [a |= b],,[b |= c] ~~{JudgmentsL}~~> [a |= c].
      unfold hom; simpl.
      apply al_subst.
      Defined.

    Definition TypesLFC : ECategory JudgmentsL (Tree ??T) (fun x y => [x|=y]).
      refine
      {| eid   := identityProof
       ; ecomp := cutProof
      |}; intros.
      apply MonoidalCat_all_central.
      apply MonoidalCat_all_central.
      unfold identityProof; unfold cutProof; simpl.
      apply al_subst_left_identity.
      unfold identityProof; unfold cutProof; simpl.
      apply al_subst_right_identity.
      unfold identityProof; unfold cutProof; simpl.
      apply al_subst_associativity'.
      Defined.

    Definition TypesEnrichedInJudgments : Enrichment.
      refine {| enr_c := TypesLFC |}.
      Defined.

    Definition Types_first c : EFunctor TypesLFC TypesLFC (fun x => x,,c ).
(*
      eapply Build_EFunctor; intros.
      eapply MonoidalCat_all_central.
      unfold eqv.
      simpl.
*)
      admit.
      Defined.

    Definition Types_second c : EFunctor TypesLFC TypesLFC (fun x => c,,x ).
      admit.
      Defined.

    Definition Types_binoidal : BinoidalCat TypesLFC (@T_Branch _).
      refine
        {| bin_first  := TypesL_first
         ; bin_second := TypesL_second
         |}.
      Defined.

    Definition Pairing : prod_obj TypesL_binoidal TypesL_binoidal -> TypesL_binoidal.
      admit.
      Defined.
    Definition Pairing_Functor : Functor (TypesL_binoidal ×× TypesL_binoidal) TypesL_binoidal Pairing.
      admit.
      Defined.
    Definition TypesL : MonoidalCat TypesL_binoidal Pairing Pairing_Functor [].
      admit.
      Defined.

    Definition TypesLEnrichedInJudgments1 : SurjectiveEnrichment.
      refine {| se_enr := TypesLEnrichedInJudgments0 |}.
      simpl.
      admit.
      Defined.

    Definition TypesLEnrichedInJudgments2 : MonoidalEnrichment.
      refine {| me_enr := TypesLEnrichedInJudgments0 ; me_mon := TypesL |}.
      simpl.
      admit.
      Defined.

    Definition TypesLEnrichedInJudgments3 : MonicMonoidalEnrichment.
      refine {| ffme_enr := TypesLEnrichedInJudgments2 |}; simpl.
      admit.
      admit.
      admit.
      Defined.

  End LanguageCategory.
   
  (*
  Definition ArrowInProgrammingLanguage (L:ProgrammingLanguage)(tc:Terminal (TypesL L)) :=
    FreydCategory (TypesL L) (TypesL L).
    *)

  Definition TwoLevelLanguage (L1 L2:ProgrammingLanguage) :=
    Reification (TypesLEnrichedInJudgments1 L1) (TypesLEnrichedInJudgments3 L2) (me_i (TypesLEnrichedInJudgments3 L2)).

  Inductive NLevelLanguage : nat -> ProgrammingLanguage -> Type :=
  | NLevelLanguage_zero : forall lang,    NLevelLanguage O lang
  | NLevelLanguage_succ : forall L1 L2 n, TwoLevelLanguage L1 L2 -> NLevelLanguage n L1 -> NLevelLanguage (S n) L2.

  Definition OmegaLevelLanguage (PL:ProgrammingLanguage) : Type :=
    forall n:nat, NLevelLanguage n PL.

  Section TwoLevelLanguage.
    Context `(L12:TwoLevelLanguage L1 L2).

    Definition FlatObject (x:TypesL L2) :=
      forall y1 y2, not ((reification_r_obj L12 y1 y2)=x).

    Definition FlatSubCategory := FullSubcategory (TypesL L2) FlatObject.

    Context `(retraction      :@Functor _ _ (TypesL L2) _ _ FlatSubCategory retract_obj).
    Context `(retraction_inv  :@Functor _ _ FlatSubCategory _ _ (TypesL L2) retract_inv_obj).
    Context  (retraction_works:retraction >>>> retraction_inv ~~~~ functor_id _).

    Definition FlatteningOfReification :=
      (garrow_from_reification (TypesLEnrichedInJudgments1 L1) (TypesLEnrichedInJudgments3 L2) L12) >>>> retraction.

    Lemma FlatteningIsNotDestructive : 
      FlatteningOfReification >>>> retraction_inv >>>> RepresentableFunctor _ (me_i (TypesLEnrichedInJudgments3 L2)) ~~~~ L12.
      admit.
      Qed.

  End TwoLevelLanguage.      
    
  Close Scope temporary_scope3.
  Close Scope al_scope.
  Close Scope nd_scope.
  Close Scope pf_scope.

End Programming_Language.

Implicit Arguments ND [ Judgment ].

(*
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
Definition mapJudg {T R:Type}(f:Tree ??T -> Tree ??R)(seq:@Judg T) : @Judg R :=
  match seq with sequentpair a b => pair (f a) (f b) end.
Implicit Arguments Judg [ ].
*)


(* proofs which are generic and apply to any acceptable langauge (most of section 4) *)
Section Programming_Language_Facts.

  (* the ambient language about which we are proving facts *)
  Context `(Lang : @ProgrammingLanguage T Rule).

  (* just for this section *)
  Open Scope nd_scope.
  Open Scope al_scope.
  Open Scope pf_scope.
  Notation "H /⋯⋯/ C" := (@ND Judg Rule H C)     : temporary_scope4.
  Notation "a === b"  := (@ndr_eqv _ _ al_eqv _ _ a b)                   : temporary_scope4.
  Open Scope temporary_scope4.

  Definition lang_al_eqv := al_eqv(ProgrammingLanguage:=Lang).
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

  Close Scope temporary_scope4.
  Close Scope al_scope.
  Close Scope nd_scope.
  Close Scope pf_scope.
  Close Scope isomorphism_scope.
End Programming_Language_Facts.

(*Coercion AL_SurjectiveEnrichment    : ProgrammingLanguage >-> SurjectiveEnrichment.*)
(*Coercion AL_MonicMonoidalEnrichment : ProgrammingLanguage >-> MonicMonoidalEnrichment.*)
*)