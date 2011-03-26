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
Require Import InitialTerminal_ch2_2.
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
Require Import FunctorCategories_ch7_7.

Require Import NaturalDeduction.
Require Import NaturalDeductionCategory.

Require Import FreydCategories.

Require Import Reification.
Require Import GeneralizedArrow.
Require Import GeneralizedArrowFromReification.
Require Import ReificationFromGeneralizedArrow.

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

  (*
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
  { al_eqv                : @ND_Relation Judg Rule where "pf1 === pf2" := (@ndr_eqv _ _ al_eqv _ _ pf1 pf2)
  ; al_tsr                : TreeStructuralRules
  ; al_subst              : CutRule
  ; al_sequent_join       : SequentJoin
  }.
  Notation "pf1 === pf2" := (@ndr_eqv _ _ al_eqv _ _ pf1 pf2) : temporary_scope3.

  Section LanguageCategory.

    Context (PL:ProgrammingLanguage).

    (* category of judgments in a fixed type/coercion context *)
    Definition Judgments_cartesian := @Judgments_Category_CartesianCat _ Rule al_eqv.

    Definition JudgmentsL          := Judgments_cartesian.

    Definition identityProof t : [] ~~{JudgmentsL}~~> [t |= t].
      unfold hom; simpl.
      apply nd_rule.
      apply al_reflexive_seq.
      Defined.

    Definition cutProof a b c : [a |= b],,[b |= c] ~~{JudgmentsL}~~> [a |= c].
      unfold hom; simpl.
      apply al_subst.
      Defined.

    Definition TypesL : ECategory JudgmentsL (Tree ??T) (fun x y => [x|=y]).
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

    Definition Types_first c : EFunctor TypesL TypesL (fun x => x,,c ).
      (*
      eapply Build_EFunctor; intros.
      eapply MonoidalCat_all_central.
      unfold eqv.
      simpl.
      *)
      admit.
      Defined.

    Definition Types_second c : EFunctor TypesL TypesL (fun x => c,,x ).
      admit.
      Defined.

    Definition Types_binoidal : BinoidalCat TypesL (@T_Branch _).
      refine
        {| bin_first  := Types_first
         ; bin_second := Types_second
         |}.
      Defined.

    Definition TypesL_binoidal : BinoidalCat TypesL (@T_Branch _).
    admit.
    Defined.

    Definition Types_PreMonoidal : PreMonoidalCat TypesL_binoidal [].
    admit.
    Defined.

    Definition TypesEnrichedInJudgments : Enrichment.
      refine {| enr_c := TypesL |}.
      Defined.

    Structure HasProductTypes :=
    {
    }.

    (* need to prove that if we have cartesian tuples we have cartesian contexts *)
    Definition LanguagesWithProductsAreSMME : HasProductTypes -> SurjectiveMonicMonoidalEnrichment TypesEnrichedInJudgments.
      admit.
      Defined.

  End LanguageCategory.

  Structure ProgrammingLanguageSMME :=
  { plsmme_pl   : ProgrammingLanguage
  ; plsmme_smme : SurjectiveMonicMonoidalEnrichment (TypesEnrichedInJudgments plsmme_pl)
  }.
  Coercion plsmme_pl : ProgrammingLanguageSMME >-> ProgrammingLanguage.
  Coercion plsmme_smme : ProgrammingLanguageSMME >-> SurjectiveMonicMonoidalEnrichment.

  Section ArrowInLanguage.
    Context  (Host:ProgrammingLanguageSMME).
    Context `(CC:CartesianCat (me_mon Host)).
    Context `(K:@ECategory _ _ _ _ _ _ (@car_mn _ _ _ _ _ _ _ CC) C Kehom).
    Context `(pmc:PreMonoidalCat K bobj mobj (@one _ _ _ (cartesian_terminal C))).
      (* FIXME *)
      (*
      Definition ArrowInProgrammingLanguage := 
        @FreydCategory _ _ _ _ _ _ (@car_mn _ _ _ _ _ _ _ CC) _ _ _ _ pmc.
        *)
  End ArrowInLanguage.

  Section GArrowInLanguage.
    Context (Guest:ProgrammingLanguageSMME).
    Context (Host :ProgrammingLanguageSMME).
    Definition GeneralizedArrowInLanguage := GeneralizedArrow Guest Host.

    (* FIXME
    Definition ArrowsAreGeneralizedArrows : ArrowInProgrammingLanguage -> GeneralizedArrowInLanguage.
    *)
    Definition TwoLevelLanguage := Reification Guest Host (me_i Host).

    Context (GuestHost:TwoLevelLanguage).

    Definition FlatObject (x:TypesL Host) :=
      forall y1 y2, not ((reification_r_obj GuestHost y1 y2)=x).

    Definition FlatSubCategory := FullSubcategory (TypesL Host) FlatObject.

    Section Flattening.

      Context  (F:Retraction (TypesL Host) FlatSubCategory).
      Definition FlatteningOfReification := garrow_from_reification Guest Host GuestHost >>>> F.
      Lemma FlatteningIsNotDestructive : 
        FlatteningOfReification >>>> retraction_retraction F >>>> RepresentableFunctor _ (me_i Host) ~~~~ GuestHost.
        admit.
        Qed.

    End Flattening.

  End GArrowInLanguage.

  Inductive NLevelLanguage : nat -> ProgrammingLanguageSMME -> Type :=
  | NLevelLanguage_zero : forall lang,    NLevelLanguage O lang
  | NLevelLanguage_succ : forall (L1 L2:ProgrammingLanguageSMME) n,
    TwoLevelLanguage L1 L2 -> NLevelLanguage n L1 -> NLevelLanguage (S n) L2.

  Definition OmegaLevelLanguage : Type :=
    { f : nat -> ProgrammingLanguageSMME
    & forall n, TwoLevelLanguage (f n) (f (S n)) }.
    
  Close Scope temporary_scope3.
  Close Scope al_scope.
  Close Scope nd_scope.
  Close Scope pf_scope.

End Programming_Language.

Implicit Arguments ND [ Judgment ].
