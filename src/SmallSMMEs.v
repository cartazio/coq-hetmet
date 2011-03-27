(*********************************************************************************************************************************)
(* SmallSMMEs:                                                                                                                   *)
(*                                                                                                                               *)
(*         The collection of SMMEs is a collection of small categories (see SmallCategories)                                     *)
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
Require Import GeneralizedArrow.
Require Import WeakFunctorCategory.


Definition SMMEs : SmallCategories.
  refine {| small_cat       := SMME
          ; small_cat_cat   := fun smme => enr_v smme
          |}.
  Defined.
