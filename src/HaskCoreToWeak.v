(*********************************************************************************************************************************)
(* HaskCoreToWeak: convert HaskCore to HaskWeak                                                                                  *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Coq.Lists.List.
Require Import HaskGeneral.
Require Import HaskLiterals.
Require Import HaskCoreVars.
Require Import HaskCoreTypes.
Require Import HaskCore.
Require Import HaskWeakVars.
Require Import HaskWeak.

Variable coreVarToWeakVar      : CoreVar  -> WeakVar.   Extract Inlined Constant coreVarToWeakVar    => "coreVarToWeakVar".

(* detects our crude Core-encoding of modal type introduction/elimination forms *)
Definition isBrak (ce:CoreExpr CoreVar) : ??WeakTypeVar :=
match ce with
  | (CoreEApp (CoreEApp (CoreEVar v) (CoreEType (TyVarTy ec))) (CoreEType tbody))
    => if coreName_eq hetmet_brak_name (coreVarCoreName v) then
      match coreVarToWeakVar v with
        | WExprVar _  => None
        | WTypeVar tv => Some tv
        | WCoerVar _  => None
      end else None
  | _ => None
end.
Definition isEsc (ce:CoreExpr CoreVar) : ??WeakTypeVar :=
match ce with
  | (CoreEApp (CoreEApp (CoreEVar v) (CoreEType (TyVarTy ec))) (CoreEType tbody))
    => if coreName_eq hetmet_esc_name (coreVarCoreName v) then
      match coreVarToWeakVar v with
        | WExprVar _  => None
        | WTypeVar tv => Some tv
        | WCoerVar _  => None
      end else None
  | _ => None
end.

Definition coreCoercionToWeakCoercion (cc:CoreCoercion) : WeakCoercion :=
  let (t1,t2) := coreCoercionKind cc
  in  weakCoercion t1 t2 cc.

Fixpoint coreExprToWeakExpr (ce:CoreExpr CoreVar) : ???WeakExpr :=
  match ce with
    | CoreELit   lit   => OK (WELit lit)
    | CoreENote  n e   => coreExprToWeakExpr e >>= fun e' => OK (WENote n e')
    | CoreEType  t     => Error "encountered CoreEType in a position where an Expr should have been"
    | CoreECast  e co  => coreExprToWeakExpr e >>= fun e' =>
                            OK (WECast e' (coreCoercionToWeakCoercion co))

    | CoreEVar   v     => match coreVarToWeakVar v with
                            | WExprVar ev => OK (WEVar ev)
                            | WTypeVar _  => Error "found a type variable inside an EVar!"
                            | WCoerVar _  => Error "found a coercion variable inside an EVar!"
                          end

    | CoreEApp   e1 e2 => match isBrak e1 with
                            | Some tv => coreExprToWeakExpr e2 >>= fun e' => OK (WEBrak tv e')
                            | None    => match isEsc e1 with
                                           | Some tv => coreExprToWeakExpr e2 >>= fun e' => OK (WEEsc tv e')
                                           | None    => coreExprToWeakExpr e1 >>= fun e1' =>
                                             match e2 with
                                               | CoreEType t => OK (WETyApp e1' t)
                                               | _           => coreExprToWeakExpr e2 >>= fun e2' => OK (WEApp e1' e2')
                                             end
                                         end
                          end

    | CoreELam   v e => match coreVarToWeakVar v with
                         | WExprVar ev => coreExprToWeakExpr e >>= fun e' => OK (WELam   ev e')
                         | WTypeVar tv => coreExprToWeakExpr e >>= fun e' => OK (WETyLam tv e')
                         | WCoerVar cv => coreExprToWeakExpr e >>= fun e' => OK (WECoLam cv e')
                       end

    | CoreELet   (CoreNonRec v ve) e => match coreVarToWeakVar v with
                         | WExprVar ev => coreExprToWeakExpr ve >>= fun ve' =>
                                            coreExprToWeakExpr e  >>= fun e'  => OK (WELet ev ve' e')
                         | WTypeVar _ => match e with
                                              | CoreEType t => Error "saw a type-let"
                                              | _           => Error "saw (ELet <tyvar> e) where e!=EType"
                                            end
                         | WCoerVar _ => Error "saw an (ELet <coercionVar>)"
                       end

    | CoreELet   (CoreRec rb)      e =>
      ((fix coreExprToWeakExprList (cel:list (CoreVar * (CoreExpr CoreVar))) : ???(list (WeakExprVar * WeakExpr)) :=
        match cel with
          | nil => OK nil
          | (v',e')::t => coreExprToWeakExprList t >>= fun t' =>
            match coreVarToWeakVar v' with
              | WExprVar ev => coreExprToWeakExpr e' >>= fun e' => OK ((ev,e')::t')
              | WTypeVar _  => Error "found a type variable in a recursive let"
              | WCoerVar _  => Error "found a coercion variable in a recursive let"
            end
        end) rb) >>= fun rb' =>
      coreExprToWeakExpr e >>= fun e' =>
      OK (WELetRec (unleaves' rb') e')

    | CoreECase  e v tbranches alts => 
      match coreVarToWeakVar v with
        | WTypeVar _  => Error "found a type variable in a case"
        | WCoerVar _  => Error "found a coercion variable in a case"
        | WExprVar ev => 
      coreExprToWeakExpr e
      >>= fun e' => coreTypeOfWeakExpr e' >>= fun te' =>
      match te' with
        | TyConApp _ tc lt =>
          ((fix mkBranches (branches: list (@triple AltCon (list CoreVar) (CoreExpr CoreVar)))
                : ???(list (AltCon*list WeakVar*WeakExpr)) :=
            match branches with
              | nil => OK nil
              | (mkTriple alt vars e)::rest =>
                  mkBranches rest >>= fun rest' => 
                    coreExprToWeakExpr e >>= fun e' => 
                    match alt with
                      | DEFAULT                => OK ((DEFAULT,nil,e')::rest')
                      | LitAlt lit             => OK ((LitAlt lit,nil,e')::rest')
                      | DataAlt _ _ _ _ tc' dc => OK (((DataAlt _ dc),(map coreVarToWeakVar vars),e')::rest')
                    end
            end) alts)
          >>= fun branches => coreExprToWeakExpr e
            >>= fun scrutinee =>
              list2vecOrError lt _ >>= fun lt' => 
                  OK (WELet ev scrutinee (WECase (WEVar ev) tbranches tc lt' (unleaves branches)))
        | _ => Error "found a case whose scrutinee's type wasn't a TyConApp"
      end
      end
  end.

