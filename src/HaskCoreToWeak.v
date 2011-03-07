(*********************************************************************************************************************************)
(* HaskCoreToWeak: convert HaskCore to HaskWeak                                                                                  *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import HaskGeneral.
Require Import HaskLiterals.
Require Import HaskCoreVars.
Require Import HaskCoreTypes.
Require Import HaskCore.
Require Import HaskWeak.

Fixpoint coreExprToWeakExpr (ce:CoreExpr CoreVar) : ???WeakExpr :=
  match ce with
    | CoreELit   lit   => OK (WELit lit)
    | CoreENote  n e   => coreExprToWeakExpr e >>= fun e' => OK (WENote n e')
    | CoreEType  t     => Error "encountered CoreEType in a position where an Expr should have been"
    | CoreECast  e co  => coreExprToWeakExpr e >>= fun e' => OK (WECast e' co)

    | CoreEVar   v     => match coreVarSort v with
                            | CoreExprVar _ => OK (WEVar v)
                            | CoreTypeVar _ => Error "found a type variable inside an EVar!"
                            | CoreCoerVar _ => Error "found a coercion variable inside an EVar!"
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

    | CoreELam   v e => match coreVarSort v with
                         | CoreExprVar _ => coreExprToWeakExpr e >>= fun e' => OK (WELam   v e')
                         | CoreTypeVar _ => coreExprToWeakExpr e >>= fun e' => OK (WETyLam v e')
                         | CoreCoerVar _ => coreExprToWeakExpr e >>= fun e' => OK (WECoLam v e')
                       end

    | CoreELet   (CoreNonRec v ve) e => match coreVarSort v with
                         | CoreExprVar _ => coreExprToWeakExpr ve >>= fun ve' =>
                                            coreExprToWeakExpr e  >>= fun e'  => OK (WELet v ve' e')
                         | CoreTypeVar _ => match e with
                                              | CoreEType t => Error "saw a type-let"
                                              | _           => Error "saw (ELet <tyvar> e) where e!=EType"
                                            end
                         | CoreCoerVar _ => Error "saw an (ELet <coercionVar>)"
                       end

    | CoreELet   (CoreRec rb)      e =>
      ((fix coreExprToWeakExprList (cel:list (CoreVar * (CoreExpr CoreVar))) : ???(list (CoreVar * WeakExpr)) :=
        match cel with
          | nil => OK nil
          | (v',e')::t => coreExprToWeakExprList t >>= fun t' =>
            match coreVarSort v' with
              | CoreExprVar _ => coreExprToWeakExpr e' >>= fun e' => OK ((v',e')::t')
              | CoreTypeVar _ => Error "found a type variable in a recursive let"
              | CoreCoerVar _ => Error "found a coercion variable in a recursive let"
            end
        end) rb) >>= fun rb' =>
      coreExprToWeakExpr e >>= fun e' =>
      OK (WELetRec (unleaves' rb') e')

    | CoreECase  e v tbranches alts => 
      coreExprToWeakExpr e
      >>= fun e' => coreTypeOfWeakExpr e' >>= fun te' =>
      match te' with
        | TyConApp _ tc lt =>
          ((fix mkBranches (branches: list (@triple AltCon (list CoreVar) (CoreExpr CoreVar)))
                : ???(list (AltCon*list CoreVar*WeakExpr)) :=
            match branches with
              | nil => OK nil
              | (mkTriple alt vars e)::rest =>
                  mkBranches rest
                  >>= fun rest' => 
                    coreExprToWeakExpr e >>= fun e' => 
                    match alt with
                      | DEFAULT                => OK ((DEFAULT,nil,e')::rest')
                      | LitAlt lit             => OK ((LitAlt lit,nil,e')::rest')
                      | DataAlt _ _ _ _ tc' dc => OK (((DataAlt _ dc),vars,e')::rest')
                    end
            end) alts)
          >>= fun branches => coreExprToWeakExpr e
            >>= fun scrutinee =>
              list2vecOrError lt _ >>= fun lt' => 
                OK (WELet v scrutinee (WECase (WEVar v) tbranches tc lt' (unleaves branches)))
        | _ => Error "found a case whose scrutinee's type wasn't a TyConApp"
      end
  end.

