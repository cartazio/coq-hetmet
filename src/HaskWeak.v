(*********************************************************************************************************************************)
(* HaskWeak: a non-dependently-typed but Coq-friendly version of HaskCore                                                        *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Coq.Lists.List.
Require Import HaskGeneral.
Require Import HaskLiterals.
Require Import HaskCoreVars.
Require Import HaskCoreTypes.
Require Import HaskCoreTypes.
Require Import HaskWeakVars.

Inductive WeakExpr :=
| WEVar       : WeakExprVar                                                  -> WeakExpr
| WELit       : HaskLiteral                                                  -> WeakExpr
| WELet       : WeakExprVar -> WeakExpr         -> WeakExpr                  -> WeakExpr
| WELetRec    : Tree ??(WeakExprVar * WeakExpr) -> WeakExpr                  -> WeakExpr
| WECast      : WeakExpr                        -> WeakCoercion              -> WeakExpr
| WENote      : Note                            -> WeakExpr                  -> WeakExpr
| WEApp       : WeakExpr                        -> WeakExpr                  -> WeakExpr
| WETyApp     : WeakExpr                        -> CoreType                  -> WeakExpr
| WECoApp     : WeakExpr                        -> WeakCoercion              -> WeakExpr
| WELam       : WeakExprVar                     -> WeakExpr                  -> WeakExpr
| WETyLam     : WeakTypeVar                     -> WeakExpr                  -> WeakExpr
| WECoLam     : WeakCoerVar                     -> WeakExpr                  -> WeakExpr
| WEBrak      : WeakTypeVar                     -> WeakExpr                  -> WeakExpr
| WEEsc       : WeakTypeVar                     -> WeakExpr                  -> WeakExpr
| WECase      : forall (scrutinee:WeakExpr)
                       (tbranches:CoreType)
                       {n:nat}(tc:TyCon n)
                       (type_params:vec CoreType n)
                       (alts : Tree ??(AltCon*list WeakVar*WeakExpr)),
                       WeakExpr.

(* calculate the free WeakVar's in a WeakExpr *)
Fixpoint getWeakExprFreeVars (me:WeakExpr) : list WeakExprVar :=
  match me with
    | WELit    _        =>     nil
    | WEVar    cv       => cv::nil
    | WECast   e co     =>                            getWeakExprFreeVars e
    | WENote   n e      =>                            getWeakExprFreeVars e
    | WETyApp  e t      =>                            getWeakExprFreeVars e
    | WECoApp  e co     =>                            getWeakExprFreeVars e
    | WEBrak   ec e     =>                            getWeakExprFreeVars e
    | WEEsc    ec e     =>                            getWeakExprFreeVars e
    | WELet    cv e1 e2 => mergeDistinctLists        (getWeakExprFreeVars e1) (removeFromDistinctList cv (getWeakExprFreeVars e2))
    | WEApp    e1 e2    => mergeDistinctLists        (getWeakExprFreeVars e1)                            (getWeakExprFreeVars e2)
    | WELam    cv e     => @removeFromDistinctList _ WeakExprVarEqDecidable cv (getWeakExprFreeVars e)
    | WETyLam  cv e     => getWeakExprFreeVars e
    | WECoLam  cv e     => getWeakExprFreeVars e

    (* the messy fixpoints below are required by Coq's termination conditions *)
    | WECase scrutinee tbranches n tc type_params alts =>
      mergeDistinctLists (getWeakExprFreeVars scrutinee) (
        ((fix getWeakExprFreeVarsAlts (alts:Tree ??(AltCon*list WeakVar*WeakExpr)) {struct alts} : list WeakExprVar :=
          match alts with
            | T_Leaf  None                                  => nil
            | T_Leaf (Some (DEFAULT,_,e))                   => getWeakExprFreeVars e
            | T_Leaf (Some (LitAlt lit,_,e))                => getWeakExprFreeVars e
            | T_Leaf (Some (DataAlt _ _ _ _ _ dc, vars,e))  => removeFromDistinctList' 
              (General.filter (map (fun v => match v with
                               | WExprVar ev => Some ev
                               | WTypeVar _  => None
                               | WCoerVar _  => None
              end) vars))
              (getWeakExprFreeVars e)
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

(* messy first-order capture-avoiding substitution on CoreType's *)
Fixpoint replaceCoreVar (te:CoreType)(tv:CoreVar)(tsubst:CoreType) : CoreType :=
  match te with
    | TyVarTy  tv'            => if eqd_dec tv tv' then tsubst else te
    | AppTy  t1 t2            => AppTy (replaceCoreVar t1 tv tsubst) (replaceCoreVar t2 tv tsubst)
    | FunTy    t1 t2          => FunTy (replaceCoreVar t1 tv tsubst) (replaceCoreVar t2 tv tsubst)
    | ForAllTy  tv' t         => if eqd_dec tv tv' then te else ForAllTy tv' (replaceCoreVar t tv tsubst)
    | PredTy (EqPred t1 t2)   => PredTy (EqPred (replaceCoreVar t1 tv tsubst) (replaceCoreVar t2 tv tsubst))
    | PredTy (IParam ip ty)   => PredTy (IParam ip (replaceCoreVar ty tv tsubst))
    | PredTy (ClassP _ c lt)  => PredTy (ClassP c ((fix replaceCoreDistinctList (lt:list CoreType) :=
      match lt with
        | nil => nil
        | h::t => (replaceCoreVar h tv tsubst)::(replaceCoreDistinctList t)
      end) lt))
    | TyConApp _ tc lt => TyConApp tc ((fix replaceCoreDistinctList (lt:list CoreType) :=
      match lt with
        | nil => nil
        | h::t => (replaceCoreVar h tv tsubst)::(replaceCoreDistinctList t)
      end) lt)
  end.

(* calculate the CoreType of a WeakExpr *)
Fixpoint coreTypeOfWeakExpr (ce:WeakExpr) : ???CoreType :=
  match ce with
    | WEVar   (weakExprVar v t) => OK t
    | WELit   lit   => OK (haskLiteralToCoreType lit)
    | WEApp   e1 e2 => coreTypeOfWeakExpr e1 >>= fun t' =>
                       match t' with
                         | (TyConApp 2 tc (t1::t2::nil)) =>
                           if (tyCon_eq tc ArrowTyCon)
                             then OK t2
                             else Error ("found non-function type "+++(weakTypeToString t')+++" in EApp")
                         | _ => Error ("found non-function type "+++(weakTypeToString t')+++" in EApp")
                       end
    | WETyApp e t    => coreTypeOfWeakExpr e >>= fun te =>
                        match te with
                          | ForAllTy v ct => OK (replaceCoreVar ct v t)
                          | _ => Error ("found non-forall type "+++(weakTypeToString te)+++" in ETyApp")
                        end
    | WECoApp e co   => coreTypeOfWeakExpr e >>= fun te =>
                        match te with
                          | TyConApp 2 tc ((PredTy (EqPred t1 t2))::t3::nil) =>
                            if (tyCon_eq tc ArrowTyCon)
                              then OK t3
                              else Error ("found non-coercion type "+++(weakTypeToString te)+++" in ETyApp")
                          | _ => Error ("found non-coercion type "+++(weakTypeToString te)+++" in ETyApp")
                        end
    | WELam   (weakExprVar ev vt) e => coreTypeOfWeakExpr e >>= fun t' => OK (TyConApp ArrowTyCon (vt::t'::nil))
    | WETyLam tv e => coreTypeOfWeakExpr e >>= fun t' => match tv with weakTypeVar tvc _ => OK (ForAllTy tvc t') end
    | WECoLam (weakCoerVar cv φ₁ φ₂) e =>
      coreTypeOfWeakExpr e >>= fun t' => OK (TyConApp ArrowTyCon ((PredTy (EqPred φ₁ φ₂))::t'::nil))
    | WELet   ev ve e            => coreTypeOfWeakExpr e
    | WELetRec rb e              => coreTypeOfWeakExpr e
    | WENote  n e                => coreTypeOfWeakExpr e
    | WECast  e (weakCoercion t1 t2 _) => OK t2
    | WECase  scrutinee tbranches n tc type_params alts => OK tbranches
    | WEBrak  ec e => coreTypeOfWeakExpr e >>= fun t' => match ec with weakTypeVar ecc _ =>
                                                           OK (TyConApp hetMetCodeTypeTyCon ((TyVarTy ecc)::t'::nil)) end
    | WEEsc   ec e => coreTypeOfWeakExpr e >>= fun t' => match ec with weakTypeVar ecc _ =>
      match t' with
        | (TyConApp 2 tc ((TyVarTy ec')::t''::nil)) =>
          if (tyCon_eq tc hetMetCodeTypeTyCon)
          then if eqd_dec ecc ec' then OK t''
            else Error "level mismatch in escapification"
          else Error "ill-typed escapification"
        | _ => Error "ill-typed escapification"
      end end
  end.

