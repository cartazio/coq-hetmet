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
Require Import ProgrammingLanguageGeneralizedArrow.
Require Import FreydCategories.

Require Import GeneralizedArrow.

Section ArrowInLanguage.

  (* an Arrow In A Programming Language consists of... *)

  (* a host language: *)
  Context `(Host:ProgrammingLanguage).

  (* ... for which Types(L) is cartesian: *)
  Context (center_of_TypesL:MonoidalCat (TypesL_PreMonoidal Host)).

  (* along with a full subcategory of Z(Types(L)) *)
  Context {P}(VK:FullSubcategory (Center (TypesL_PreMonoidal Host)) P).

  Context (Pobj_unit   : P []).
  Context (Pobj_closed : forall a b, P a → P b → P (bin_obj(BinoidalCat:=Center_is_PreMonoidal (TypesL_PreMonoidal Host)) a b)).
  Definition VKM :=
    PreMonoidalFullSubcategory_PreMonoidal (Center_is_PreMonoidal (TypesL_PreMonoidal Host)) VK Pobj_unit Pobj_closed.

  (* a premonoidal category enriched in aforementioned full subcategory *)
  Context (Kehom:(Center (TypesL_PreMonoidal Host)) -> (Center (TypesL_PreMonoidal Host)) -> @ob _ _ VK).
  Context (KE   :@ECategory (@ob _ _ VK) (@hom _ _ VK) VK _ VKM (pmon_I VKM) VKM (Center (TypesL_PreMonoidal Host)) Kehom).
  Context {kbo  :(Center (TypesL_PreMonoidal Host)) -> (Center (TypesL_PreMonoidal Host)) -> (Center (TypesL_PreMonoidal Host))}.
  Context (kbc  :@BinoidalCat (Center (TypesL_PreMonoidal Host)) _ (Underlying KE) kbo).

  Definition one' := @one _ _ _ (car_terminal(CartesianCat:=CC))
  Context (K :@PreMonoidalCat _ _ KE kbo kbc ).
  Context (CC:CartesianCat (Center (TypesL_PreMonoidal Host))).

  Definition ArrowInProgrammingLanguage :=
    @FreydCategory _ _ _ _ _ _ (Center (TypesL_PreMonoidal Host)) _ _ _ _ K.

  Definition ArrowsAreGeneralizedArrows (arrow:ArrowInProgrammingLanguage) : GeneralizedArrow K_enrichment Host.
    refine {| ga_functor_monoidal := inclusion_functor_monoidal VK |}.
    Defined.

End GArrowInLanguage.
