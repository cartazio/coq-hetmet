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

(* an enrichment for which every object of the enriching category is the tensor of finitely many hom-objects *)
(*
Definition SurjectiveEnrichment `(ec:ECategory(Hom:=Vhom)(V:=V)(bin_obj':=Vbobj)(EI:=EI)) :=
  @treeDecomposition _ _
                  (fun t => match t with
                            | None   => EI
                            | Some x => match x with pair y z => Vhom y z end
                            end)
                  bin_obj.
*)

(* in the paper this is called simply an "enrichment" *)
Structure PreMonoidalEnrichment :=
{ enr_v_ob       : Type
; enr_v_hom      : enr_v_ob -> enr_v_ob -> Type
; enr_v          : Category enr_v_ob enr_v_hom
; enr_v_i        : enr_v_ob
; enr_v_bobj     : enr_v -> enr_v -> enr_v
; enr_v_bin      : BinoidalCat enr_v enr_v_bobj
; enr_v_pmon     : PreMonoidalCat enr_v_bin enr_v_i
; enr_v_mon      : MonoidalCat enr_v_pmon
; enr_c_obj      : Type
; enr_c_hom      : enr_c_obj -> enr_c_obj -> enr_v
; enr_c          : ECategory enr_v_mon enr_c_obj enr_c_hom
; enr_c_bin      : EBinoidalCat enr_c
; enr_c_i        : enr_c
; enr_c_pm       : PreMonoidalCat enr_c_bin enr_c_i
}.
Coercion enr_c   : PreMonoidalEnrichment >-> ECategory.

(*
Structure MonoidalEnrichment {e:Enrichment} :=
{ me_enr         :=e
; me_fobj        : prod_obj e e -> e
; me_f           : Functor (e ×× e) e me_fobj
; me_i           : e
; me_mon         : MonoidalCat e me_fobj me_f me_i
; me_mf          : MonoidalFunctor me_mon (enr_v_mon e) (HomFunctor e me_i)
}.
Implicit Arguments MonoidalEnrichment [ ].
Coercion me_mon : MonoidalEnrichment >-> MonoidalCat.
Coercion me_enr : MonoidalEnrichment >-> Enrichment.

(* an enrichment for which hom(I,-) is monoidal, full, faithful, and conservative *)
Structure MonicMonoidalEnrichment {e}{me:MonoidalEnrichment e} :=
{ ffme_enr             := me
; ffme_mf_full         : FullFunctor         (HomFunctor e (me_i me))
; ffme_mf_faithful     : FaithfulFunctor     (HomFunctor e (me_i me))
; ffme_mf_conservative : ConservativeFunctor (HomFunctor e (me_i me))
}.
Implicit Arguments MonicMonoidalEnrichment [ ].
Coercion ffme_enr : MonicMonoidalEnrichment >-> MonoidalEnrichment.
Transparent HomFunctor.

Structure SurjectiveMonicMonoidalEnrichment (e:Enrichment) :=
{ smme_se       : SurjectiveEnrichment e
; smme_monoidal : MonoidalEnrichment e
; smme_me       : MonicMonoidalEnrichment _ smme_monoidal
}.
Coercion smme_se : SurjectiveMonicMonoidalEnrichment >-> SurjectiveEnrichment.
Coercion smme_me : SurjectiveMonicMonoidalEnrichment >-> MonicMonoidalEnrichment.

(* like SurjectiveMonicMonoidalEnrichment, but the Enrichment is a field, not a parameter *)
Structure SMME :=
{ smme_e   : Enrichment
; smme_see : SurjectiveEnrichment smme_e
; smme_mon : MonoidalEnrichment smme_e
; smme_mee : MonicMonoidalEnrichment _ smme_mon
}.
Coercion smme_e   : SMME >-> Enrichment.
Coercion smme_see : SMME >-> SurjectiveEnrichment.
Coercion smme_mon : SMME >-> MonoidalEnrichment.
Coercion smme_mee : SMME >-> MonicMonoidalEnrichment.
*)