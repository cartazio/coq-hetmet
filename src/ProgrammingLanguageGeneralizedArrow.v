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

Require Import FreydCategories.

Require Import GeneralizedArrowFromReification.
Section GArrowInLanguage.

  Definition GeneralizedArrowInLanguage (Guest:ProgrammingLanguageSMME) (Host :ProgrammingLanguageSMME)
    := GeneralizedArrow Guest Host.

  Definition ArrowsAreGeneralizedArrows (Host:ProgrammingLanguageSMME)
    {mf}{mn}{cc}{kehom}{CC}
    (arrow:ArrowInProgrammingLanguage Host _ _ CC mf mn cc kehom) :  GeneralizedArrowInLanguage.

  Definition TwoLevelLanguage := Reification Guest Host (me_i Host).

  Context (GuestHost:TwoLevelLanguage).

  Definition FlatObject (x:TypesL _ _ Host) :=
    forall y1 y2, not ((reification_r_obj GuestHost y1 y2)=x).

  Definition FlatSubCategory := FullSubcategory (TypesL _ _ Host) FlatObject.

  Section Flattening.

    Context  (F:Retraction (TypesL _ _ Host) FlatSubCategory).
    Definition FlatteningOfReification := garrow_from_reification Guest Host GuestHost >>>> F.
    Lemma FlatteningIsNotDestructive : 
      FlatteningOfReification >>>> retraction_retraction F >>>> HomFunctor _ (me_i Host) ~~~~ GuestHost.
      admit.
      Qed.

  End Flattening.

End GArrowInLanguage.
