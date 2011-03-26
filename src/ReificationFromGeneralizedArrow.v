(*********************************************************************************************************************************)
(* ReificationFromGeneralizedArrow:                                                                                              *)
(*                                                                                                                               *)
(*   Turn a reification into a generalized arrow                                                                                 *)
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
Require Import Reification.
Require Import GeneralizedArrow.

Definition reification_from_garrow (K:Enrichment) {ce} (C:MonoidalEnrichment ce) (garrow : GeneralizedArrow K C)
 : Reification K C (mon_i C).
  refine
  {| reification_r         := fun k:K => RepresentableFunctor K k >>>> garrow
   ; reification_rstar_f   :=                                garrow >>>> me_mf C
   |}.
   apply MonoidalFunctorsCompose.
   abstract (intros; set (@ni_associativity) as q; apply q).
   Defined.


