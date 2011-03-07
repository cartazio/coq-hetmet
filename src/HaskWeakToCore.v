(*********************************************************************************************************************************)
(* HaskWeakToCore: convert HaskWeak to HaskCore                                                                                  *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import HaskKinds.
Require Import HaskCoreLiterals.
Require Import HaskCoreVars.
Require Import HaskCoreTypes.
Require Import HaskCore.
Require Import HaskWeakVars.
Require Import HaskWeakTypes.
Require Import HaskWeak.
Require Import HaskCoreToWeak.

Variable mkCoreLet : @CoreBind CoreVar -> @CoreExpr CoreVar -> @CoreExpr CoreVar.
  Extract Inlined Constant mkCoreLet => "MkCore.mkCoreLet".

Variable sortAlts  : forall {a}{b}, list (@triple AltCon a b) -> list (@triple AltCon a b).
  Extract Inlined Constant mkCoreLet => "sortAlts".
  Implicit Arguments sortAlts [[a][b]].

Variable trustMeCoercion           : CoreCoercion.
  Extract Inlined Constant trustMeCoercion => "Coercion.unsafeCoerce".

(* Coercion and Type are actually the same thing in GHC, but we don't tell Coq about that.  This lets us get around it. *)
Variable coreCoercionsAreReallyTypes : CoreCoercion -> CoreType.
  Extract Inlined Constant coreCoercionsAreReallyTypes => "(\x -> x)".

(* a dummy variable which is never referenced but needed for a binder *)
Variable dummyVariable : CoreVar.
  (* FIXME this doesn't actually work *)
  Extract Inlined Constant dummyVariable => "(Prelude.error ""dummyVariable"")".

Section HaskWeakToCore.

  (* the CoreVar for the "magic" bracket/escape identifiers must be created from within one of the monads *)
  Context (hetmet_brak_var : CoreVar).
  Context (hetmet_esc_var  : CoreVar).

  (* FIXME: do something more intelligent here *)
  Definition weakCoercionToCoreCoercion : WeakCoercion -> CoreCoercion :=
    fun _ => trustMeCoercion.

  Fixpoint weakExprToCoreExpr (me:WeakExpr) : @CoreExpr CoreVar :=
  match me with
  | WEVar   (weakExprVar v _)            => CoreEVar  v
  | WELit   lit                          => CoreELit  lit
  | WEApp   e1 e2                        => CoreEApp     (weakExprToCoreExpr e1) (weakExprToCoreExpr e2)
  | WETyApp e t                          => CoreEApp     (weakExprToCoreExpr e ) (CoreEType (weakTypeToCoreType t))
  | WECoApp e co                         => CoreEApp     (weakExprToCoreExpr e )
                                                           (CoreEType (coreCoercionsAreReallyTypes (weakCoercionToCoreCoercion co)))
  | WENote  n e                          => CoreENote n  (weakExprToCoreExpr e )
  | WELam   (weakExprVar ev _  ) e       => CoreELam  ev (weakExprToCoreExpr e )
  | WETyLam (weakTypeVar tv _  ) e       => CoreELam  tv (weakExprToCoreExpr e )
  | WECoLam (weakCoerVar cv _ _) e       => CoreELam  cv (weakExprToCoreExpr e )
  | WECast  e co                         => CoreECast    (weakExprToCoreExpr e ) (weakCoercionToCoreCoercion co)
  | WEBrak  (weakTypeVar ec _) e t       => CoreEApp  (CoreEApp (CoreEVar hetmet_brak_var)
                                                           (CoreEType (TyVarTy ec))) (CoreEType (weakTypeToCoreType t))
  | WEEsc   (weakTypeVar ec _) e t       => CoreEApp  (CoreEApp (CoreEVar hetmet_esc_var)
                                                           (CoreEType (TyVarTy ec))) (CoreEType (weakTypeToCoreType t))
  | WELet   (weakExprVar v _) ve e       => mkCoreLet      (CoreNonRec v (weakExprToCoreExpr ve))  (weakExprToCoreExpr e)
  | WECase  e tbranches tc types alts    => CoreECase (weakExprToCoreExpr e) dummyVariable (weakTypeToCoreType tbranches)
                                              (sortAlts ((
                                                fix mkCaseBranches (alts:Tree 
                                                  ??(AltCon*list WeakTypeVar*list WeakCoerVar*list WeakExprVar*WeakExpr)) :=
                                                match alts with
                                                  | T_Leaf None              => nil
                                                  | T_Branch b1 b2           => app (mkCaseBranches b1) (mkCaseBranches b2)
                                                  | T_Leaf (Some (ac,tvars,cvars,evars,e)) =>
                                                    (mkTriple (ac:AltCon)
                                                      (app (app 
                                                        (map (fun v:WeakTypeVar => weakVarToCoreVar v) tvars)
                                                        (map (fun v:WeakCoerVar => weakVarToCoreVar v) cvars))
                                                      (map (fun v:WeakExprVar => weakVarToCoreVar v) evars))
                                                      (weakExprToCoreExpr e))::nil
                                                end
                                              ) alts))
  | WELetRec mlr e                       => CoreELet (CoreRec
                                               ((fix mkLetBindings (mlr:Tree ??(WeakExprVar * WeakExpr)) :=
                                                 match mlr with
                                                   | T_Leaf None                        => nil
                                                   | T_Leaf (Some (weakExprVar cv _,e)) => (cv,(weakExprToCoreExpr e))::nil
                                                   | T_Branch b1 b2                     => app (mkLetBindings b1) (mkLetBindings b2)
                                                 end) mlr))
                                               (weakExprToCoreExpr e)
  end.

End HaskWeakToCore.


