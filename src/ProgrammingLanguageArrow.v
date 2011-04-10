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

Require Import ProgrammingLanguage.
Require Import ProgrammingLanguageGeneralizedArrow.
Require Import FreydCategories.

Require Import GeneralizedArrow.

Section ArrowInLanguage.

  (* an Arrow In A Programming Language consists of... *)

  (* a host language: *)
  Context `(Host:ProgrammingLanguage).

  (* ... for which Types(L) is cartesian: *)
  Context {MF}(center_of_TypesL:MonoidalCat (TypesL _ _ Host) (fun x => (fst_obj _ _ x),,(snd_obj _ _ x)) MF []).

  (* along with a monoidal subcategory of Z(Types(L)) *)
  Context (VK:MonoidalSubCat center_of_TypesL).

  (* a premonoidal category enriched in aforementioned full subcategory *)
  Context (Kehom:center_of_TypesL -> center_of_TypesL -> @ob _ _ VK).

  Context (KE:@ECategory (@ob _ _ VK) (@hom _ _ VK) VK _ VK
               (mon_i (full_subcat_is_monoidal VK)) (full_subcat_is_monoidal VK) center_of_TypesL Kehom).

  Context {kbo:center_of_TypesL -> center_of_TypesL -> center_of_TypesL}.

  Context (kbc:@BinoidalCat center_of_TypesL _ (Underlying KE) kbo).

  Check (@PreMonoidalCat)
  Definition one' := @one _ _ _ (car_terminal(CartesianCat:=CC))
  Context (K:@PreMonoidalCat _ _ KE kbo kbc ).
  Context (CC:CartesianCat center_of_TypesL).

  (*
  Definition K_enrichment : Enrichment.
    refine {| enr_c := KE |}.
    Defined.
  Context (K_surjective:SurjectiveEnrichment K_enrichment).
    *)

  Definition ArrowInProgrammingLanguage :=
    @FreydCategory _ _ _ _ _ _ center_of_TypesL _ _ _ _ K.

  Definition ArrowsAreGeneralizedArrows (arrow:ArrowInProgrammingLanguage) : GeneralizedArrow K_enrichment Host.
    refine {| ga_functor_monoidal := inclusion_functor_monoidal VK |}.
    Defined.

End GArrowInLanguage.
