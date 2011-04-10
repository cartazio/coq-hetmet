(*********************************************************************************************************************************)
(* Enrichments                                                                                                                   *)
(*                                                                                                                               *)
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
Require Import BinoidalCategories.
Require Import PreMonoidalCategories.
Require Import PreMonoidalCenter.
Require Import RepresentableStructure_ch7_2.
Require Import WeakFunctorCategory.

(* in the paper this is called simply an "enrichment" *)
Structure Enrichment :=
{ enr_v_ob         :  Type
; enr_v_hom        :  enr_v_ob -> enr_v_ob -> Type
; enr_v            :  Category enr_v_ob enr_v_hom
; enr_v_i          :  enr_v_ob
; enr_v_bobj       :  enr_v -> enr_v -> enr_v
; enr_v_bin        :  BinoidalCat enr_v enr_v_bobj
; enr_v_pmon       :  PreMonoidalCat enr_v_bin enr_v_i
; enr_v_mon        :  MonoidalCat enr_v_pmon
; enr_c_obj        :  Type
; enr_c_hom        :  enr_c_obj -> enr_c_obj -> enr_v
; enr_c            :  ECategory enr_v_mon enr_c_obj enr_c_hom
; enr_c_bin        :  EBinoidalCat enr_c
; enr_c_i          :  enr_c
; enr_c_pm         :  PreMonoidalCat enr_c_bin enr_c_i
; enr_c_center     := Center enr_c_bin
; enr_c_center_mon := Center_is_Monoidal enr_c_pm
}.
Coercion enr_c   : Enrichment >-> ECategory.

(* Coq grinds down into a performance bog when I try to use this *)
Definition WeaklySurjectiveEnrichment (ec:Enrichment) :=
  @treeDecomposition (enr_v ec) (option (ec*ec))
                  (fun t => match t with
                            | None   => enr_v_i ec
                            | Some x => match x with pair y z => enr_c_hom ec y z end
                            end)
                  (enr_v_bobj ec).

(* technically this ought to be a "strictly surjective enrichment" *)
Structure SurjectiveEnrichment :=
{ senr_c_obj      :  Type
; senr_v_ob       := Tree ??(senr_c_obj * senr_c_obj)
; senr_c_hom      := fun (c1 c2:senr_c_obj) => [(c1, c2)]
; senr_v_hom      :  senr_v_ob -> senr_v_ob -> Type
; senr_v          :  Category senr_v_ob senr_v_hom
; senr_v_i        := []
; senr_v_bobj     := @T_Branch ??(senr_c_obj * senr_c_obj)
; senr_v_bin      :  BinoidalCat senr_v senr_v_bobj
; senr_v_pmon     :  PreMonoidalCat senr_v_bin senr_v_i
; senr_v_mon      :  MonoidalCat senr_v_pmon
; senr_c          :  ECategory senr_v_mon senr_c_obj senr_c_hom
; senr_c_bin      :  EBinoidalCat senr_c
; senr_c_i        :  senr_c
; senr_c_pm       :  PreMonoidalCat senr_c_bin senr_c_i
}.

Definition SurjectiveEnrichmentToEnrichment (se:SurjectiveEnrichment) : Enrichment.
refine
{| enr_v_ob      := senr_v_ob se
; enr_v_hom      := senr_v_hom se
; enr_v          := senr_v se
; enr_v_i        := senr_v_i se
; enr_v_bobj     := senr_v_bobj se
; enr_v_bin      := senr_v_bin se
; enr_v_pmon     := senr_v_pmon se
; enr_v_mon      := senr_v_mon se
; enr_c_obj      := senr_c_obj se
; enr_c_hom      := senr_c_hom se
; enr_c          := senr_c se
; enr_c_bin      := senr_c_bin se
; enr_c_i        := senr_c_i se
; enr_c_pm       := senr_c_pm se
|}.
Defined.
Coercion SurjectiveEnrichmentToEnrichment : SurjectiveEnrichment >-> Enrichment.

Definition MonoidalEnrichment (e:Enrichment) :=
  PreMonoidalFunctor
    (enr_c_pm e)
    (enr_v_pmon e)
    (HomFunctor e (pmon_I (enr_c_pm e))).

Class MonicEnrichment {e:Enrichment} :=
{ me_enr          := e
; me_homfunctor   := HomFunctor e (enr_c_i e)
; me_full         :  FullFunctor         me_homfunctor
; me_faithful     :  FaithfulFunctor     me_homfunctor
; me_conservative :  ConservativeFunctor me_homfunctor
(*; me_homfunctor_c := RestrictDomain me_homfunctor (enr_c_center e)*)
}.
Implicit Arguments MonicEnrichment [ ].
Coercion me_enr : MonicEnrichment >-> Enrichment.
Transparent HomFunctor.

(* like SurjectiveMonicMonoidalEnrichment, but the Enrichment is a field, not a parameter *)
Structure SMME :=
{ smme_e   : SurjectiveEnrichment
; smme_mon : MonoidalEnrichment smme_e
; smme_mee : MonicEnrichment smme_e
}.
Coercion smme_e   : SMME >-> SurjectiveEnrichment.
Coercion smme_mon : SMME >-> MonoidalEnrichment.

Definition SMMEs : SmallCategories.
  refine {| small_cat       := SMME
          ; small_cat_cat   := fun smme => enr_v smme
          |}.
  Defined.
