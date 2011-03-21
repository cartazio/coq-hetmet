(*********************************************************************************************************************************)
(* HaskStrongCategory:                                                                                                           *)
(*                                                                                                                               *)
(*    Well-typed Haskell terms in a specific tyvar/covar context form a category                                                 *)
(*                                                                                                                               *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import NaturalDeduction.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import HaskKinds.
Require Import HaskCoreTypes.
Require Import HaskLiteralsAndTyCons.
Require Import HaskStrongTypes.
Require Import HaskStrong.

(*  
    (* the category of flat Haskell terms (n-ary) *)
    Section HaskFlat.
  
      Context (past:@Past V).
    
      Lemma idmor   a : [] ~~{SystemFC_Cat_Flat past}~~> [(a,a)].
        (*set (@nd_rule _ Rule (RVar Γ a past)) as q.*)
        admit.
        Defined.
    
      Lemma compmor a b c : [(a,b)],,[(b,c)] ~~{SystemFC_Cat_Flat past}~~> [(a,c)].
        admit.
        Defined.
      
      Definition HaskFlat
        : ECategory
            (SystemFC_Cat_Flat past)
            (Tree ??(@CoreType V))
            (fun a s => [(a,s)]).
        refine
          {| eid   := fun a     => idmor   a
           ; ecomp := fun a b c => compmor a b c
          |}; intros; simpl in *; auto.
        apply (MonoidalCat_all_central (SystemFC_Cat_Flat past)).
        apply (MonoidalCat_all_central (SystemFC_Cat_Flat past)).
        admit.
        admit.
        admit.
        Defined.
  
      Definition HaskFlatEnrichment : SurjectiveEnrichment.
        refine {| se_enr := {| enr_c := HaskFlat |} |}.
        admit.
        Defined.
  
    End HaskFlat.
  
    (* the category of multi-level Haskell terms (n-ary) with a given past *)
    Section Hask.
      Context (past:@Past V).
  
      Lemma idmor'   a : [] ~~{SystemFC_Cat past}~~> [(a,a)].
        (*set (@nd_rule _ Rule (RVar Γ a past)) as q.*)
        admit.
        Defined.
    
      Lemma compmor' a b c : [(a,b)],,[(b,c)] ~~{SystemFC_Cat past}~~> [(a,c)].
        admit.
        Defined.
  
      Definition Hask
        : ECategory
            (SystemFC_Cat past)
            (Tree ??(@LeveledHaskType V))
            (fun a s => [(a,s)]).
        refine
          {| eid   := fun a     => idmor'   a
           ; ecomp := fun a b c => compmor' a b c
          |}; intros; simpl in *; auto.
        apply (MonoidalCat_all_central (SystemFC_Cat past)).
        apply (MonoidalCat_all_central (SystemFC_Cat past)).
        admit.
        admit.
        admit.
        Defined.
  
      Definition HaskEnrichmentMonoidal : MonoidalEnrichment.
        refine {| me_enr := {| enr_c := Hask |} |}.
        Admitted.
  
      Definition HaskEnrichmentMonicMonoidal : MonicMonoidalEnrichment.
        refine {| ffme_enr := HaskEnrichmentMonoidal |}.
        admit.
        admit.
        admit.
        Defined.
    End Hask.
  
    Section ReificationAndGeneralizedArrow.
      Context
        (past:list ((Tree ??(@LeveledHaskType V)) * V))
        (Σ:(Tree ??(@LeveledHaskType V)))
        (n:V).
    
      Definition SystemFC_Reification 
        : Reification
        (HaskFlatEnrichment (((Σ,n)::past))) 
        (HaskEnrichmentMonicMonoidal  (*past*))
        (me_i (HaskEnrichmentMonicMonoidal (*past*))).
        (* refine {| reification_rstar_f := EscBrak_Functor Γ past n Σ |}.*)
        admit.
        Defined.
(*    
      Definition SystemFC_GArrow :=
        garrow_from_reification
        (HaskFlatEnrichment (((Σ,n)::past)))
        (HaskEnrichmentMonicMonoidal (*past*))
        SystemFC_Reification.
  *)
      (* I think we have to add a proof that the derived GArrow's range is in the "monoidal closure" of the reification functor;
       * from there we can show that -- in the case of Hask and System FC -- that range is a retract of some other subcategory
       * of Hask which consists of the (GArrow g => g a b) morphisms *)
    
    End ReificationAndGeneralizedArrow.
*)  


