(*********************************************************************************************************************************)
(* HaskWeak: a non-dependently-typed but Coq-friendly version of HaskCore                                                        *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Coq.Lists.List.
Require Import HaskKinds.
Require Import HaskLiterals.
Require Import HaskTyCons.
Require Import HaskCoreVars.
Require Import HaskWeakVars.
Require Import HaskWeakTypes.

Inductive WeakAltCon :=
| WeakDataAlt : CoreDataCon  -> WeakAltCon
| WeakLitAlt  : HaskLiteral  -> WeakAltCon
| WeakDEFAULT :                 WeakAltCon.

Inductive WeakExpr :=
| WEVar       : WeakExprVar                                                  -> WeakExpr
| WELit       : HaskLiteral                                                  -> WeakExpr

(* TO DO: add a WEWhere and use the source location to detect which one the user used *)
| WELet       : WeakExprVar -> WeakExpr         -> WeakExpr                  -> WeakExpr
| WELetRec    : Tree ??(WeakExprVar * WeakExpr) -> WeakExpr                  -> WeakExpr
| WECast      : WeakExpr                        -> WeakCoercion              -> WeakExpr
| WENote      : Note                            -> WeakExpr                  -> WeakExpr
| WEApp       : WeakExpr                        -> WeakExpr                  -> WeakExpr
| WETyApp     : WeakExpr                        -> WeakType                  -> WeakExpr
| WECoApp     : WeakExpr                        -> WeakCoercion              -> WeakExpr
| WELam       : WeakExprVar                     -> WeakExpr                  -> WeakExpr
(*
| WEKappa     : WeakExprVar                     -> WeakExpr                  -> WeakExpr
| WEKappaApp  : WeakExpr                        -> WeakExpr                  -> WeakExpr
*)
| WETyLam     : WeakTypeVar                     -> WeakExpr                  -> WeakExpr
| WECoLam     : WeakCoerVar                     -> WeakExpr                  -> WeakExpr

(* The WeakType argument in WEBrak/WEEsc is used only when going back      *)
(* from Weak to Core; it lets us dodge a possibly-failing type             *)
(* calculation.  The CoreVar argument is the GlobalVar for the hetmet_brak *)
(* or hetmet_esc identifier                                                *)
| WEBrak      : WeakExprVar -> WeakTypeVar          -> WeakExpr  -> WeakType     -> WeakExpr
| WEEsc       : WeakExprVar -> WeakTypeVar          -> WeakExpr  -> WeakType     -> WeakExpr
| WECSP       : WeakExprVar -> WeakTypeVar          -> WeakExpr  -> WeakType     -> WeakExpr

| WECase      : forall (vscrut:WeakExprVar)
                       (scrutinee:WeakExpr)
                       (tbranches:WeakType)
                       (tc:TyCon)
                       (type_params:list WeakType)
                       (alts : Tree ??(WeakAltCon*list WeakTypeVar*list WeakCoerVar*list WeakExprVar*WeakExpr)),
                       WeakExpr.

Definition weakTypeOfLiteral (lit:HaskLiteral) : WeakType :=
  (WTyCon (haskLiteralToTyCon lit)).

(*
Fixpoint weakExprVarOccursFree (wvf:WeakExprVar)(we:WeakExpr) : bool :=
  match we with
  | WEVar   wv                           => if eqd_dec (wvf:CoreVar) (wv:CoreVar) then true else false
  | WELit   lit                          => false
  | WEApp   e1 e2                        => weakExprVarOccursFree wvf e1 || weakExprVarOccursFree wvf e2
  | WETyApp e t                          => weakExprVarOccursFree wvf e
  | WECoApp e co                         => weakExprVarOccursFree wvf e
  | WENote  n e                          => weakExprVarOccursFree wvf e
  | WELam   ev e                         => if eqd_dec (wvf:CoreVar) (ev:CoreVar) then false else weakExprVarOccursFree wvf e
  | WETyLam tv e                         => weakExprVarOccursFree wvf e
  | WECoLam cv e                         => weakExprVarOccursFree wvf e
  | WECast  e co                         => weakExprVarOccursFree wvf e
  | WEBrak  v wtv e t                    => weakExprVarOccursFree wvf e
  | WEEsc   v wtv e t                    => weakExprVarOccursFree wvf e
  | WECSP   v wtv e t                    => weakExprVarOccursFree wvf e
  | WELet   v ebind ebody                => weakExprVarOccursFree wvf ebind
                                            || if eqd_dec (wvf:CoreVar) (v:CoreVar) then false else weakExprVarOccursFree wvf ebody
  | WECase  vs es tb tc tys alts         =>
    if weakExprVarOccursFree wvf es
      then true
      else (fix weakExprVarOccursFreeBranches (alts:Tree ??(_)) : bool :=
        match alts with
          | T_Leaf None     => false
          | T_Leaf (Some (_,_,_,v',e')) => 
            if fold_left bor (map (fun v'':WeakExprVar => if eqd_dec (wvf:CoreVar) (v'':CoreVar) then true else false ) v') false
              then false
              else weakExprVarOccursFree wvf e'
          | T_Branch b1 b2  => weakExprVarOccursFreeBranches b1 ||
            weakExprVarOccursFreeBranches b2
        end) alts
  | WELetRec mlr e                       => false
  end.

(* some very simple-minded cleanups to produce "prettier" expressions *)
Fixpoint simplifyWeakExpr (me:WeakExpr) : WeakExpr :=
  match me with
  | WEVar   wv                           => WEVar wv
  | WELit   lit                          => WELit lit
  | WEApp   e1 e2                        => WEApp        (simplifyWeakExpr e1) (simplifyWeakExpr e2)
  | WETyApp e t                          => WETyApp      (simplifyWeakExpr e ) t
  | WECoApp e co                         => CoreEApp     (simplifyWeakExpr e ) co
  | WENote  n e                          => CoreENote n  (simplifyWeakExpr e )
  | WELam   ev e                         => CoreELam  ev (simplifyWeakExpr e )
  | WETyLam tv e                         => CoreELam  tv (simplifyWeakExpr e )
  | WECoLam cv e                         => CoreELam  cv (simplifyWeakExpr e )
  | WECast  e co                         => CoreECast    (simplifyWeakExpr e ) co
  | WEBrak  v wtv e t                    => WEBrak v wtv (simplifyWeakExpr e ) t
  | WEEsc   v wtv e t                    => WEEsc  v wtv (simplifyWeakExpr e ) t
  | WECSP   v wtv e t                    => WECSP  v wtv (simplifyWeakExpr e ) t
  | WELet   v ebind ebody                => WELet  v (simplifyWeakExpr ebind) (simplifyWeakExpr ebody)
  | WECase  vs es tb tc tys alts         => WECase vs es tb tc tys (* FIXME alts *)
  (* un-letrec-ify multi branch letrecs *)
  | WELetRec mlr e                       => WELetRec mlr (simplifyWeakExpr e )
  end.
*)
