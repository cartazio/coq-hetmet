(*********************************************************************************************************************************)
(* HaskTyCons: representation of type constructors, type functions, and data constructors                                        *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Coq.Strings.String.
Require Import HaskKinds.

Variable CoreDataCon     : Type.                      Extract Inlined Constant CoreDataCon          => "DataCon.DataCon".

(* once again, we pull the trick of having multiple Coq types map to a single Haskell type to provide stronger typing *)
Variable TyCon           : Type.                      Extract Inlined Constant TyCon                => "TyCon.TyCon".
Variable TyFun           : Type.                      Extract Inlined Constant TyFun                => "TyCon.TyCon".

Variable CoreName        : Type.                      Extract Inlined Constant CoreName              => "Name.Name".
Variable Class_          : Type.                      Extract Inlined Constant Class_                => "Class.Class".
Variable CoreIPName      : Type -> Type.              Extract         Constant CoreIPName "’a"       => "BasicTypes.IPName".
                                                      Extraction Inline CoreIPName.

Variable tyConToString   : TyCon   -> string.     Extract Inlined Constant tyConToString         => "outputableToString".
Variable tyFunToString   : TyFun   -> string.     Extract Inlined Constant tyFunToString         => "outputableToString".
Instance TyConToString   : ToString TyCon := { toString := tyConToString }.
Instance TyFunToString   : ToString TyFun := { toString := tyFunToString }.
Instance TyConToLatex    : ToLatex  TyCon := { toLatex  := fun x => toLatex (toString x) }.
Instance TyFunToLatex    : ToLatex  TyCon := { toLatex  := fun x => toLatex (toString x) }.

Variable ModalBoxTyCon   : TyCon.        Extract Inlined Constant ModalBoxTyCon => "TysWiredIn.hetMetCodeTypeTyCon".
Variable PairTyCon       : TyFun.        Extract Inlined Constant PairTyCon     => "TysWiredIn.pairTyCon".
Variable UnitTyCon       : TyFun.        Extract Inlined Constant UnitTyCon     => "TysWiredIn.unitTyCon".
Variable ArrowTyCon      : TyCon.        Extract Constant ArrowTyCon    => "Type.funTyCon".
