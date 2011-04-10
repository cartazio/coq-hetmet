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
Require Import PreMonoidalCategories.
Require Import MonoidalCategories_ch7_8.
Require Import Coherence_ch7_8.
Require Import Enrichment_ch2_8.
Require Import Enrichments.
Require Import RepresentableStructure_ch7_2.
Require Import Reification.
Require Import GeneralizedArrow.

Definition reification_from_garrow (K:Enrichment) {ce} (C:MonoidalEnrichment ce) (garrow : GeneralizedArrow K C)
 : Reification K ce (enr_c_i ce).
  refine
  {| reification_r         := fun k:K => HomFunctor K k >>>> ga_functor garrow
   ; reification_rstar_f   :=                                ga_functor garrow >>>> C
   ; reification_rstar     := PreMonoidalFunctorsCompose garrow C
   |}.
   abstract (intros; set (@ni_associativity) as q; apply q).
   Defined.



