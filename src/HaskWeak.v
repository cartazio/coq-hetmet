(*********************************************************************************************************************************)
(* HaskWeak: a non-dependently-typed but Coq-friendly version of HaskCore                                                        *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import HaskGeneral.
Require Import HaskLiterals.
Require Import HaskCoreVars.
Require Import HaskCoreTypes.

Inductive WeakExpr :=
| WEVar       : CoreVar                                                  -> WeakExpr
| WELit       : HaskLiteral                                              -> WeakExpr
| WELet       : CoreVar -> WeakExpr         -> WeakExpr                  -> WeakExpr
| WELetRec    : Tree ??(CoreVar * WeakExpr) -> WeakExpr                  -> WeakExpr
| WECast      : WeakExpr                    -> CoreCoercion              -> WeakExpr
| WENote      : Note                        -> WeakExpr                  -> WeakExpr
| WEApp       : WeakExpr                    -> WeakExpr                  -> WeakExpr
| WETyApp     : WeakExpr                    -> CoreType                  -> WeakExpr
| WECoApp     : WeakExpr                    -> CoreCoercion              -> WeakExpr
| WELam       : CoreVar                     -> WeakExpr                  -> WeakExpr
| WETyLam     : CoreVar                     -> WeakExpr                  -> WeakExpr
| WECoLam     : CoreVar                     -> WeakExpr                  -> WeakExpr
| WEBrak      : CoreVar                     -> WeakExpr                  -> WeakExpr
| WEEsc       : CoreVar                     -> WeakExpr                  -> WeakExpr
| WECase      : forall (scrutinee:WeakExpr)
                       (tbranches:CoreType)
                       {n:nat}(tc:TyCon n)
                       (type_params:vec CoreType n)
                       (alts : Tree ??(AltCon*list CoreVar*WeakExpr)),
                       WeakExpr.

(* calculate the free CoreVar's in a WeakExpr *)
Fixpoint getWeakExprFreeVars (me:WeakExpr) : list CoreVar :=
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
    | WELam    cv e     => removeFromDistinctList cv (getWeakExprFreeVars e)
    | WETyLam  cv e     => removeFromDistinctList cv (getWeakExprFreeVars e)
    | WECoLam  cv e     => removeFromDistinctList cv (getWeakExprFreeVars e)

    (* the messy fixpoints below are required by Coq's termination conditions *)
    | WECase scrutinee tbranches n tc type_params alts =>
      mergeDistinctLists (getWeakExprFreeVars scrutinee) (
        ((fix getWeakExprFreeVarsAlts (alts:Tree ??(AltCon*list CoreVar*WeakExpr)) {struct alts} : list CoreVar :=
          match alts with
            | T_Leaf  None                                  => nil
            | T_Leaf (Some (DEFAULT,_,e))                   => getWeakExprFreeVars e
            | T_Leaf (Some (LitAlt lit,_,e))                => getWeakExprFreeVars e
            | T_Leaf (Some (DataAlt _ _ _ _ _ dc, vars,e))  => removeFromDistinctList' vars (getWeakExprFreeVars e)
            | T_Branch b1 b2                        => mergeDistinctLists (getWeakExprFreeVarsAlts b1) (getWeakExprFreeVarsAlts b2)
          end) alts))
    | WELetRec mlr e => (fix removeVarsLetRec (mlr:Tree ??(CoreVar * WeakExpr))(cvl:list CoreVar) :=
      match mlr with
        | T_Leaf None          => cvl
        | T_Leaf (Some (cv,e)) => removeFromDistinctList cv cvl
        | T_Branch b1 b2       => removeVarsLetRec b1 (removeVarsLetRec b2 cvl)
      end) mlr (mergeDistinctLists (getWeakExprFreeVars e) 
        ((fix getWeakExprFreeVarsLetRec (mlr:Tree ??(CoreVar * WeakExpr)) :=
          match mlr with
            | T_Leaf None          => nil
            | T_Leaf (Some (cv,e)) => getWeakExprFreeVars e
            | T_Branch b1 b2       => mergeDistinctLists (getWeakExprFreeVarsLetRec b1) (getWeakExprFreeVarsLetRec b2)
          end) mlr))
  end.

(* wrap lambdas around an expression until it has no free variables *)
Definition makeClosedExpression : WeakExpr -> WeakExpr :=
  fun me => (fix closeExpression (me:WeakExpr)(cvl:list CoreVar) :=
  match cvl with
    | nil      => me
    | cv::cvl' => WELam cv (closeExpression me cvl')
  end) me (getWeakExprFreeVars me).

(* messy first-order capture-avoiding substitution on CoreType's *)
Fixpoint replaceCoreVar (te:CoreType)(tv:CoreVar)(tsubst:CoreType) :=
  match te with
    | TyVarTy  tv'            => if eqd_dec tv tv' then tsubst else te
    | AppTy    t1 t2          => AppTy (replaceCoreVar t1 tv tsubst) (replaceCoreVar t2 tv tsubst)
    | FunTy    t1 t2          => FunTy (replaceCoreVar t1 tv tsubst) (replaceCoreVar t2 tv tsubst)
    | ForAllTy tv' t          => if eqd_dec tv tv' then te else ForAllTy tv' (replaceCoreVar t tv tsubst)
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
    | WEVar   v     => match coreVarSort v with
                         | CoreExprVar t => OK t
                         | CoreTypeVar _ => Error "found tyvar in expression"
                         | CoreCoerVar _ => Error "found coercion variable in expression"
                       end
    | WELit   lit   => OK (haskLiteralToCoreType lit)
    | WEApp   e1 e2 => coreTypeOfWeakExpr e1 >>= fun t' =>
                       match t' with
                         | FunTy t1 t2 => OK t2
                         | (TyConApp 2 tc (t1::t2::nil)) =>
                           if (tyCon_eq tc ArrowTyCon)
                             then OK t2
                             else Error ("found non-function type "+++(coreTypeToString t')+++" in EApp")
                         | _ => Error ("found non-function type "+++(coreTypeToString t')+++" in EApp")
                       end
    | WETyApp e t    => coreTypeOfWeakExpr e >>= fun te =>
                        match te with
                          | ForAllTy v ct => match coreVarSort v with
                                               | CoreExprVar _ => Error "found an expression variable inside an forall-type!"
                                               | CoreTypeVar _ => OK (replaceCoreVar ct v t)
                                               | CoreCoerVar _ => Error "found a coercion variable inside an forall-type!"
                                             end
                          | _ => Error ("found non-forall type "+++(coreTypeToString te)+++" in ETyApp")
                        end
    | WECoApp e co   => coreTypeOfWeakExpr e >>= fun te =>
                        match te with
                          | FunTy (PredTy (EqPred t1 t2)) t3 => OK t3
                          | TyConApp 2 tc ((PredTy (EqPred t1 t2))::t3::nil) =>
                            if (tyCon_eq tc ArrowTyCon)
                              then OK t3
                              else Error ("found non-coercion type "+++(coreTypeToString te)+++" in ETyApp")
                          | _ => Error ("found non-coercion type "+++(coreTypeToString te)+++" in ETyApp")
                        end
    | WELam   ev e => coreTypeOfWeakExpr e >>= fun t' => match coreVarSort ev with
                                               | CoreExprVar vt => OK (FunTy vt t')
                                               | CoreTypeVar _  => Error "found a type variable in a WELam!"
                                               | CoreCoerVar _  => Error "found a coercion variable in a WELam!"
                                             end
    | WETyLam tv e => coreTypeOfWeakExpr e >>= fun t' => OK (ForAllTy tv t')
    | WECoLam cv e => coreTypeOfWeakExpr e >>= fun t' => match coreVarSort cv with
                                               | CoreExprVar vt => Error "found an expression variable in a WECoLam!"
                                               | CoreTypeVar _  => Error "found a type variable in a WECoLam!"
                                               | CoreCoerVar (φ₁,φ₂) => OK (FunTy (PredTy (EqPred φ₁ φ₂)) t')
                                             end
    | WELet   ev ve e            => coreTypeOfWeakExpr e
    | WELetRec rb e              => coreTypeOfWeakExpr e
    | WENote  n e                => coreTypeOfWeakExpr e
    | WECast  e co               => OK (snd (coreCoercionKind co))
    | WECase  scrutinee tbranches n tc type_params alts => OK tbranches
    | WEBrak  ec e => coreTypeOfWeakExpr e >>= fun t' => OK (TyConApp hetMetCodeTypeTyCon ((TyVarTy ec)::t'::nil))
    | WEEsc   ec e => coreTypeOfWeakExpr e >>= fun t' =>
      match t' with
        | (TyConApp 2 tc ((TyVarTy ec')::t''::nil)) =>
          if (tyCon_eq tc hetMetCodeTypeTyCon)
          then if eqd_dec ec ec' then OK t''
            else Error "level mismatch in escapification"
          else Error "ill-typed escapification"
        | _ => Error "ill-typed escapification"
      end
  end.

