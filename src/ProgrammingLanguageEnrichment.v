(*********************************************************************************************************************************)
(* ProgrammingLanguageEnrichment                                                                                                 *)
(*                                                                                                                               *)
(*   Types are enriched in Judgments.                                                                                            *)
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
Require Import BinoidalCategories.
Require Import PreMonoidalCategories.
Require Import MonoidalCategories_ch7_8.
Require Import Coherence_ch7_8.
Require Import Enrichment_ch2_8.
Require Import RepresentableStructure_ch7_2.
Require Import FunctorCategories_ch7_7.

Require Import Enrichments.
Require Import NaturalDeduction.
Require Import NaturalDeductionCategory.
Require Import ProgrammingLanguageCategory.
        Export ProgrammingLanguageCategory.

Section ProgrammingLanguageEnrichment.

  Context `(PL:ProgrammingLanguage).

  Definition TypesEnrichedInJudgments : SurjectiveEnrichment.
    refine
      {| senr_c_pm     := TypesL_PreMonoidal PL
       ; senr_v        := JudgmentsL PL
       ; senr_v_bin    := Judgments_Category_binoidal _
       ; senr_v_pmon   := Judgments_Category_premonoidal _
       ; senr_v_mon    := Judgments_Category_monoidal _
       ; senr_c_bin    := Types_binoidal PL
       ; senr_c        := TypesL PL
      |}.
      Defined.

End ProgrammingLanguageEnrichment.

