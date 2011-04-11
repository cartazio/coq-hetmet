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
Require Import BinoidalCategories.
Require Import PreMonoidalCategories.
Require Import PreMonoidalCenter.
Require Import MonoidalCategories_ch7_8.
Require Import Coherence_ch7_8.
Require Import Enrichment_ch2_8.
Require Import RepresentableStructure_ch7_2.
Require Import FunctorCategories_ch7_7.

Require Import NaturalDeduction.
Require Import NaturalDeductionCategory.

Require Import ProgrammingLanguage.
Require Import FreydCategories.
Require Import Enrichments.
Require Import GeneralizedArrow.

Section ArrowInLanguage.

  (* an Arrow In A Programming Language consists of... *)

  (* a host language: *)
  Context `(Host         : ProgrammingLanguage).

  Context  (Host_Monoidal  : MonoidalCat  (TypesL_PreMonoidal Host)).
  Context  (Host_Cartesian : CartesianCat Host_Monoidal).

  Context
    {P}
    (Pobj_unit   : P [])
    (Pobj_closed : forall a b, P a → P b → P (bin_obj(BinoidalCat:=Center_is_PreMonoidal (TypesL_PreMonoidal Host)) a b)).

  Context (VK : FullSubcategory Host_Cartesian P).

  Context  ehom KE (K_bin:@EBinoidalCat _ _ VK _ _ _
          (PreMonoidalFullSubcategory_PreMonoidal Host_Cartesian VK Pobj_unit Pobj_closed)
          (TypesL Host) ehom KE (bin_obj(BinoidalCat:=Host_Monoidal))).

  Context (K_premonoidal:PreMonoidalCat K_bin (one(TerminalObject:=Host_Cartesian))).

  Definition ArrowInProgrammingLanguage :=
    @FreydCategory _ _ _ _ _ _ _ _ Host_Cartesian _ _ K_bin K_premonoidal.

  Definition K_enrichment : Enrichment.
    refine
      {| enr_c_pm  := K_premonoidal
       ; enr_v_mon := MonoidalFullSubcategory_Monoidal Host_Cartesian _ _ VK
      |}.
      Defined.

  Instance ArrowsAreGeneralizedArrows : GeneralizedArrow K_enrichment (TypesEnrichedInJudgments Host) :=
    { ga_functor_monoidal :=
        PreMonoidalFullSubcategoryInclusionFunctor_PreMonoidal Host_Cartesian VK Pobj_unit Pobj_closed Host_Cartesian }.

End ArrowInLanguage.
