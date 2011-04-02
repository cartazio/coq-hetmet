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

Section ExtendFunctor.

  Context `(F:Functor).
  Context  (P:c1 -> Prop).

  Definition domain_subcat := FullSubcategory c1 P.

  Definition functor_restricts_to_full_subcat_on_domain_fobj (a:domain_subcat) : c2 :=
    F (projT1 a).

  Definition functor_restricts_to_full_subcat_on_domain_fmor (a b:domain_subcat)(f:a~~{domain_subcat}~~>b) :
    (functor_restricts_to_full_subcat_on_domain_fobj a)~~{c2}~~>(functor_restricts_to_full_subcat_on_domain_fobj b) :=
    F \ (projT1 f).

  Lemma functor_restricts_to_full_subcat_on_domain : Functor domain_subcat c2 functor_restricts_to_full_subcat_on_domain_fobj.
    refine {| fmor := functor_restricts_to_full_subcat_on_domain_fmor |};
      unfold functor_restricts_to_full_subcat_on_domain_fmor; simpl; intros.
    setoid_rewrite H; reflexivity.
    setoid_rewrite fmor_preserves_id; reflexivity.
    setoid_rewrite <- fmor_preserves_comp; reflexivity.
    Defined.

End ExtendFunctor.

Section MonoidalSubCat.

  (* a monoidal subcategory is a full subcategory, closed under tensor and containing the unit object *)
  Class MonoidalSubCat {Ob}{Hom}{C:Category Ob Hom}{MFobj}{MF}{MI}(MC:MonoidalCat C MFobj MF MI) :=
  { msc_P                   :  MC -> Prop
  ; msc_closed_under_tensor :  forall o1 o2, msc_P o1 -> msc_P o2 -> msc_P (MC (pair_obj o1 o2))
  ; msc_contains_unit       :  msc_P (mon_i MC)
  ; msc_subcat              := FullSubcategory MC msc_P
  }.
  Local Coercion msc_subcat : MonoidalSubCat >-> SubCategory.

  Context `(MSC:MonoidalSubCat).

  (* any full subcategory of a monoidal category, , is itself monoidal *)
  Definition mf_restricts_to_full_subcat_on_domain_fobj (a:MSC ×× MSC) : MSC.
    destruct a.
    destruct o.
    destruct o0.
    set (MC (pair_obj x x0)) as m'.
    exists m'.
    apply msc_closed_under_tensor; auto.
    Defined.

  Definition mf_restricts_to_full_subcat_on_domain_fmor
    {a}{b}
    (f:a~~{MSC ×× MSC}~~>b)
    :
    (mf_restricts_to_full_subcat_on_domain_fobj a)~~{MSC}~~>(mf_restricts_to_full_subcat_on_domain_fobj b).
    destruct a as [[a1 a1pf] [a2 a2pf]].
    destruct b as [[b1 b1pf] [b2 b2pf]].
    destruct f as [[f1 f1pf] [f2 f2pf]].
    simpl in *.
    exists (MC \ (pair_mor (pair_obj a1 a2) (pair_obj b1 b2) f1 f2)); auto.
    Defined.

  Lemma mf_restricts_to_full_subcat_on_domain : Functor (MSC ×× MSC) MSC
    mf_restricts_to_full_subcat_on_domain_fobj.
    refine {| fmor := fun a b f => mf_restricts_to_full_subcat_on_domain_fmor f |};
      unfold functor_restricts_to_full_subcat_on_domain_fmor; simpl; intros.
    admit.
    admit.
    admit.
    Defined.

  Definition subcat_i : MSC.
    exists (mon_i MC).
    apply msc_contains_unit.
    Defined.

  Lemma full_subcat_is_monoidal : MonoidalCat MSC _ mf_restricts_to_full_subcat_on_domain subcat_i.
    admit.
    Defined.

  Lemma inclusion_functor_monoidal : MonoidalFunctor full_subcat_is_monoidal MC (InclusionFunctor _ MSC).
    admit.
    Defined.

End MonoidalSubCat.
Coercion full_subcat_is_monoidal : MonoidalSubCat >-> MonoidalCat.

Section ArrowInLanguage.

  (* an Arrow In A Programming Language consists of... *)

  (* a host language: *)
  Context (Host:ProgrammingLanguageSMME).

  (* ... for which Types(L) is cartesian: *)
  Context {MF}(center_of_TypesL:MonoidalCat (TypesL _ _ Host) (fun x => (fst_obj _ _ x),,(snd_obj _ _ x)) MF []).

  (* along with a monoidal subcategory of Z(Types(L)) *)
  Context (VK:MonoidalSubCat center_of_TypesL).

  (* a premonoidal category enriched in aforementioned full subcategory *)
  Context {Kehom:center_of_TypesL -> center_of_TypesL -> VK}.

  Context {KE:@ECategory _ _ VK _ _ _ VK center_of_TypesL Kehom}.

  Context (CC:CartesianCat center_of_TypesL).

  Context {kbo}{kbc}(K:@PreMonoidalCat _ _ KE kbo kbc (@one _ _ _ (car_terminal(CartesianCat:=CC)))).

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
