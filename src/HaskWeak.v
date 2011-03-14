(*********************************************************************************************************************************)
(* HaskWeak: a non-dependently-typed but Coq-friendly version of HaskCore                                                        *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Coq.Lists.List.
Require Import HaskKinds.
Require Import HaskCoreLiterals.
Require Import HaskCore.
Require Import HaskCoreVars.
Require Import HaskCoreTypes.
Require Import HaskCoreTypes.
Require Import HaskWeakVars.
Require Import HaskWeakTypes.

Inductive WeakExpr :=
| WEVar       : WeakExprVar                                                  -> WeakExpr
| WELit       : HaskLiteral                                                  -> WeakExpr
| WELet       : WeakExprVar -> WeakExpr         -> WeakExpr                  -> WeakExpr
| WELetRec    : Tree ??(WeakExprVar * WeakExpr) -> WeakExpr                  -> WeakExpr
| WECast      : WeakExpr                        -> WeakCoercion              -> WeakExpr
| WENote      : Note                            -> WeakExpr                  -> WeakExpr
| WEApp       : WeakExpr                        -> WeakExpr                  -> WeakExpr
| WETyApp     : WeakExpr                        -> WeakType                  -> WeakExpr
| WECoApp     : WeakExpr                        -> WeakCoercion              -> WeakExpr
| WELam       : WeakExprVar                     -> WeakExpr                  -> WeakExpr
| WETyLam     : WeakTypeVar                     -> WeakExpr                  -> WeakExpr
| WECoLam     : WeakCoerVar                     -> WeakExpr                  -> WeakExpr

(* The WeakType argument in WEBrak/WEEsc is used only when going back      *)
(* from Weak to Core; it lets us dodge a possibly-failing type             *)
(* calculation.  The CoreVar argument is the GlobalVar for the hetmet_brak *)
(* or hetmet_esc identifier                                                *)
| WEBrak      : CoreVar -> WeakTypeVar          -> WeakExpr  -> WeakType     -> WeakExpr
| WEEsc       : CoreVar -> WeakTypeVar          -> WeakExpr  -> WeakType     -> WeakExpr

| WECase      : forall (vscrut:WeakExprVar)
                       (scrutinee:WeakExpr)
                       (tbranches:WeakType)
                       (tc:TyCon)
                       (type_params:list WeakType)
                       (alts : Tree ??(AltCon*list WeakTypeVar*list WeakCoerVar*list WeakExprVar*WeakExpr)),
                       WeakExpr.

(* calculate the free WeakVar's in a WeakExpr *)
(*
Fixpoint getWeakExprFreeVars (me:WeakExpr) : list WeakExprVar :=
  match me with
    | WELit    _        =>     nil
    | WEVar    cv       => cv::nil
    | WECast   e co     =>                            getWeakExprFreeVars e
    | WENote   n e      =>                            getWeakExprFreeVars e
    | WETyApp  e t      =>                            getWeakExprFreeVars e
    | WECoApp  e co     =>                            getWeakExprFreeVars e
    | WEBrak   ec e _   =>                            getWeakExprFreeVars e
    | WEEsc    ec e _   =>                            getWeakExprFreeVars e
    | WELet    cv e1 e2 => mergeDistinctLists        (getWeakExprFreeVars e1) (removeFromDistinctList cv (getWeakExprFreeVars e2))
    | WEApp    e1 e2    => mergeDistinctLists        (getWeakExprFreeVars e1)                            (getWeakExprFreeVars e2)
    | WELam    cv e     => @removeFromDistinctList _ WeakExprVarEqDecidable cv (getWeakExprFreeVars e)
    | WETyLam  cv e     => getWeakExprFreeVars e
    | WECoLam  cv e     => getWeakExprFreeVars e

    (* the messy fixpoints below are required by Coq's termination conditions; trust me, I tried to get rid of them *)
    | WECase scrutinee tbranches tc type_params alts =>
      mergeDistinctLists (getWeakExprFreeVars scrutinee) (
        ((fix getWeakExprFreeVarsAlts (alts:Tree ??(AltCon*list WeakTypeVar*list WeakCoerVar*list WeakExprVar*WeakExpr))
          {struct alts} : list WeakExprVar :=
          match alts with
            | T_Leaf  None                                  => nil
            | T_Leaf (Some (DEFAULT,_,_,_,e))                   => getWeakExprFreeVars e
            | T_Leaf (Some (LitAlt lit,_,_,_,e))                => getWeakExprFreeVars e
            | T_Leaf (Some ((DataAlt dc), tvars, cvars, evars,e))  => removeFromDistinctList' evars (getWeakExprFreeVars e)
            | T_Branch b1 b2                        => mergeDistinctLists (getWeakExprFreeVarsAlts b1) (getWeakExprFreeVarsAlts b2)
          end) alts))
    | WELetRec mlr e => (fix removeVarsLetRec (mlr:Tree ??(WeakExprVar * WeakExpr))(cvl:list WeakExprVar) :=
      match mlr with
        | T_Leaf None          => cvl
        | T_Leaf (Some (cv,e)) => removeFromDistinctList cv cvl
        | T_Branch b1 b2       => removeVarsLetRec b1 (removeVarsLetRec b2 cvl)
      end) mlr (mergeDistinctLists (getWeakExprFreeVars e) 
        ((fix getWeakExprFreeVarsLetRec (mlr:Tree ??(WeakExprVar * WeakExpr)) :=
          match mlr with
            | T_Leaf None          => nil
            | T_Leaf (Some (cv,e)) => getWeakExprFreeVars e
            | T_Branch b1 b2       => mergeDistinctLists (getWeakExprFreeVarsLetRec b1) (getWeakExprFreeVarsLetRec b2)
          end) mlr))
  end.

(* wrap lambdas around an expression until it has no free expression variables *)
Definition makeClosedExpression : WeakExpr -> WeakExpr :=
  fun me => (fix closeExpression (me:WeakExpr)(cvl:list WeakExprVar) :=
  match cvl with
    | nil      => me
    | cv::cvl' => WELam cv (closeExpression me cvl')
  end) me (getWeakExprFreeVars me).
*)
Definition weakTypeOfLiteral (lit:HaskLiteral) : WeakType :=
  (WTyCon (haskLiteralToTyCon lit)).

Variable coreTypeOfCoreExpr    : @CoreExpr CoreVar -> CoreType.
  Extract Inlined Constant coreTypeOfCoreExpr => "CoreUtils.exprType".
