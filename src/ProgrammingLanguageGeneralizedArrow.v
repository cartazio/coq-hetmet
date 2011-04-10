(*********************************************************************************************************************************)
(* ProgrammingLanguageArrow                                                                                                      *)
(*                                                                                                                               *)
(*   Arrows in ProgrammingLanguages.                                                                                             *)
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

Require Import Enrichments.
Require Import Reification.
Require Import GeneralizedArrow.
Require Import ProgrammingLanguage.

Section ProgrammingLanguageGeneralizedArrow.

  Context
  `(Guest        : ProgrammingLanguage)
  `(Host         : ProgrammingLanguage)
   (HostMonoidal : MonoidalEnrichment (TypesEnrichedInJudgments Host))
   (HostMonic    : MonicEnrichment    (TypesEnrichedInJudgments Host)).

  Definition GeneralizedArrowInLanguage 
    := GeneralizedArrow (TypesEnrichedInJudgments Guest) HostMonoidal.

End ProgrammingLanguageGeneralizedArrow.

