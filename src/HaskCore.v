(*********************************************************************************************************************************)
(* HaskCore: basically GHC's CoreSyn.Expr imported into Coqland                                                                  *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Coq.Strings.String.
Require Import HaskGeneral.
Require Import HaskLiterals.
Require Import HaskCoreTypes.
Require Import HaskCoreVars.

(* this type must extract to EXACTLY match TypeRep.Type *)
Inductive CoreExpr {b:Type} :=
| CoreEVar   : CoreVar                          -> CoreExpr
| CoreELit   : HaskLiteral                      -> CoreExpr
| CoreEApp   : CoreExpr        ->  CoreExpr     -> CoreExpr
| CoreELam   : b               ->  CoreExpr     -> CoreExpr
| CoreELet   : CoreBind        ->  CoreExpr     -> CoreExpr
| CoreECase  : CoreExpr   -> b ->  CoreType     -> list (@triple AltCon (list b) CoreExpr) -> CoreExpr
| CoreECast  : CoreExpr        ->  CoreCoercion -> CoreExpr
| CoreENote  : Note            ->  CoreExpr     -> CoreExpr
| CoreEType  : CoreType                         -> CoreExpr
with      CoreBind {b:Type} :=
| CoreNonRec : b -> CoreExpr         -> CoreBind  
| CoreRec    : list (b * CoreExpr  ) -> CoreBind.
Extract Inductive CoreExpr =>
   "CoreSyn.Expr" [
      "CoreSyn.Var"
      "CoreSyn.Lit"
      "CoreSyn.App"
      "CoreSyn.Lam"
      "CoreSyn.Let"
      "CoreSyn.Case"
      "CoreSyn.Cast"
      "CoreSyn.Note"
      "CoreSyn.Type" ].
Extract Inductive CoreBind =>
  "CoreSyn.Bind" [ "CoreSyn.NonRec" "CoreSyn.Rec" ].

(* extracts the Name from a CoreVar *)
Variable coreVarCoreName    : CoreVar -> CoreName.   Extract Inlined Constant coreVarCoreName  => "Var.varName".

Extract Constant ArrowTyCon           => "Type.funTyCon".     (* Figure 7, (->) *)
Extract Constant CoFunConst           => "TyCon.TyCon".                        Extraction Implicit CoFunConst [ 1 ].
Extract Constant TyFunConst           => "TyCon.TyCon".                        Extraction Implicit TyFunConst [ 1 ].

(*Extract Inlined Constant getDataCons => "TyCon.tyConDataCons".*)
Variable mkTyConApp : forall n, TyCon n -> list CoreType -> CoreType.
  Extract Inlined Constant mkTyConApp => "Type.mkTyConApp".

(* the magic wired-in name for the modal type introduction form *)
Variable hetmet_brak_name   : CoreName.              Extract Inlined Constant hetmet_brak_name => "PrelNames.hetmet_brak_name".

(* the magic wired-in name for the modal type elimination form *)
Variable hetmet_esc_name    : CoreName.              Extract Inlined Constant hetmet_esc_name  => "PrelNames.hetmet_esc_name".


