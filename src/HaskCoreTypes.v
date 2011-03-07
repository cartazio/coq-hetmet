(*********************************************************************************************************************************)
(* HaskCoreTypes: basically GHC's TypeRep.Type imported into Coqland                                                             *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Coq.Strings.String.
Require Import HaskGeneral.
Require Import HaskLiterals.
Require Import HaskCoreVars.

Variable CoreName           : Type.                                               Extract Inlined Constant CoreName => "Name.Name".
Variable coreName_eq        : forall (a b:CoreName),   sumbool (a=b) (not (a=b)). Extract Inlined Constant coreName_eq => "(==)".
Axiom    coreName_eq_refl   : ∀ v, (coreName_eq v v)=(left _ (refl_equal v)).
Instance CoreNameEqDecidable : EqDecidable CoreName :=
{ eqd_dec            := coreName_eq
}.

Inductive CoreIPName        : Type -> Type := .                               Extract Inductive CoreIPName => "CoreSyn.IPName" [ ].

(* this exracts onto TypeRep.Type, on the nose *)
Inductive CoreType :=
| TyVarTy  :             CoreVar                   -> CoreType
| AppTy    :             CoreType ->      CoreType -> CoreType   (* first arg must be AppTy or TyVarTy*)
| TyConApp : forall {n}, TyCon n  -> list CoreType -> CoreType
| FunTy    :             CoreType ->      CoreType -> CoreType   (* technically redundant since we have FunTyCon *)
| ForAllTy :             CoreVar  ->      CoreType -> CoreType
| PredTy   :             PredType                  -> CoreType
with PredType :=
| ClassP   : forall {n}, Class_ n            -> list CoreType -> PredType
| IParam   :             CoreIPName CoreName -> CoreType      -> PredType
| EqPred   :             CoreType            -> CoreType      -> PredType.
Extract Inductive CoreType =>
   "TypeRep.Type" [ "TypeRep.TyVarTy" "TypeRep.AppTy" "TypeRep.TyConApp" "TypeRep.FunTy" "TypeRep.ForAllTy" "TypeRep.PredTy" ].
Extract Inductive PredType =>
   "TypeRep.PredType" [ "TypeRep.ClassP" "TypeRep.IParam" "TypeRep.EqPred" ].

Variable coreTypeToString      : CoreType     -> string.    Extract Inlined Constant coreTypeToString       => "outputableToString".
Variable coreNameToString      : CoreName     -> string.    Extract Inlined Constant coreNameToString       => "outputableToString".

Variable CoreCoercion          : Type.                      Extract Inlined Constant CoreCoercion           => "Coercion.Coercion".
Variable coreCoercionToString  : CoreCoercion -> string.    Extract Inlined Constant coreCoercionToString   => "outputableToString".
Variable coreCoercionKind      : CoreCoercion -> CoreType*CoreType.
 Extract Inlined Constant coreCoercionKind => "Coercion.coercionKind".

Variable coretype_eq_dec : forall (c1 c2:CoreType), sumbool (eq c1 c2) (not (eq c1 c2)).
  Extract Inlined Constant coretype_eq_dec => "Type.coreEqType".
  Instance CoreTypeEqDecidable : EqDecidable CoreType.
    apply Build_EqDecidable.
    apply coretype_eq_dec.
    Defined.

Variable kindOfCoreType : CoreType -> Kind.      Extract Inlined Constant kindOfCoreType => "(coreKindToKind . Coercion.typeKind)".
