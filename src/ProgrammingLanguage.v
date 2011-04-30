(*********************************************************************************************************************************)
(* ProgrammingLanguage                                                                                                           *)
(*                                                                                                                               *)
(*   Basic assumptions about programming languages.                                                                              *)
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

Require Import NaturalDeduction.

Section Programming_Language.

  Context {T    : Type}.               (* types of the language *)

  Definition PLJudg := (Tree ??T) * (Tree ??T).
  Definition sequent := @pair (Tree ??T) (Tree ??T).
     Notation "cs |= ss" := (sequent cs ss) : pl_scope.

  Context {Rule : Tree ??PLJudg -> Tree ??PLJudg -> Type}.

  Notation "H /⋯⋯/ C" := (ND Rule H C) : pl_scope.

  Open Scope pf_scope.
  Open Scope nd_scope.
  Open Scope pl_scope.

  Class ProgrammingLanguage :=
  { pl_eqv0               :> @ND_Relation PLJudg Rule
  ; pl_snd                :> @SequentND PLJudg Rule _ sequent
  ; pl_cnd                :> @ContextND PLJudg Rule T sequent pl_snd
  ; pl_eqv1               :> @SequentND_Relation PLJudg Rule _ sequent pl_snd pl_eqv0
  ; pl_eqv                :> @ContextND_Relation PLJudg Rule _ sequent pl_snd pl_cnd pl_eqv0 pl_eqv1
  }.
  Notation "pf1 === pf2" := (@ndr_eqv _ _ pl_eqv _ _ pf1 pf2) : temporary_scope3.
  Coercion pl_eqv  : ProgrammingLanguage >-> ContextND_Relation.
  Coercion pl_cnd  : ProgrammingLanguage >-> ContextND.

End Programming_Language.

