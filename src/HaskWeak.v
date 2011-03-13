(*********************************************************************************************************************************)
(* HaskWeak: a non-dependently-typed but Coq-friendly version of HaskCore                                                        *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Coq.Lists.List.
Require Import HaskKinds.
Require Import HaskCoreLiterals.
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

(* the WeakType argument in WEBrak/WEEsc is used only when going back    *)
(* from Weak to Core; it lets us dodge a possibly-failing type           *)
(* calculation                                                           *)
| WEBrak      : WeakTypeVar                     -> WeakExpr  -> WeakType     -> WeakExpr
| WEEsc       : WeakTypeVar                     -> WeakExpr  -> WeakType     -> WeakExpr

(* note that HaskWeak "Case" does not bind a variable; coreExprToWeakExpr adds a let-binder *)
| WECase      : forall (scrutinee:WeakExpr)
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

(* calculate the CoreType of a WeakExpr *)
Fixpoint weakTypeOfWeakExpr (ce:WeakExpr) : ???WeakType :=
  match ce with
    | WEVar   (weakExprVar v t) => OK t
    | WELit   lit   => OK (weakTypeOfLiteral lit)
    | WEApp   e1 e2 => weakTypeOfWeakExpr e1 >>= fun t' =>
                       match t' with
                         | (WAppTy (WAppTy WFunTyCon t1) t2) => OK t2
                         | _ => Error ("found non-function type "+++t'+++" in EApp")
                       end
    | WETyApp e t    => weakTypeOfWeakExpr e >>= fun te =>
                        match te with
                          | WForAllTy v ct => OK (replaceWeakTypeVar ct v t)
                          | _ => Error ("found non-forall type "+++te+++" in ETyApp")
                        end
    | WECoApp e co   => weakTypeOfWeakExpr e >>= fun te =>
                        match te with
                          | WCoFunTy t1 t2 t => OK t
                          | _ => Error ("found non-coercion type "+++te+++" in ETyApp")
                        end
    | WELam   (weakExprVar ev vt) e => weakTypeOfWeakExpr e >>= fun t' => OK (WAppTy (WAppTy WFunTyCon vt) t')
    | WETyLam tv e => weakTypeOfWeakExpr e >>= fun t' => OK (WForAllTy tv t')
    | WECoLam (weakCoerVar cv φ₁ φ₂) e => weakTypeOfWeakExpr e >>= fun t' => OK (WCoFunTy φ₁ φ₂ t')
    | WELet   ev ve e            => weakTypeOfWeakExpr e
    | WELetRec rb e              => weakTypeOfWeakExpr e
    | WENote  n e                => weakTypeOfWeakExpr e
    | WECast  e (weakCoercion t1 t2 _) => OK t2
    | WECase  scrutinee tbranches tc type_params alts => OK tbranches

    (* note that we willfully ignore the type stashed in WEBrak/WEEsc here *)
    | WEBrak  ec e _ => weakTypeOfWeakExpr e >>= fun t' => OK (WCodeTy ec t')
    | WEEsc   ec e _ => weakTypeOfWeakExpr e >>= fun t' =>
      match t' with
        | (WAppTy (WAppTy WCodeTyCon (WTyVarTy ec')) t'') =>
          if eqd_dec ec ec' then OK t''
            else Error "level mismatch in escapification"
        | _ => Error "ill-typed escapification"
      end
  end.

