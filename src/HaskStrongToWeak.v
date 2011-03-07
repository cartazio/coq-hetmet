(*********************************************************************************************************************************)
(* HaskStrongToWeak: convert HaskStrong to HaskWeak                                                                              *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import NaturalDeduction.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Specif.
Require Import HaskKinds.
Require Import HaskCoreLiterals.
Require Import HaskWeakTypes.
Require Import HaskWeakVars.
Require Import HaskWeak.
Require Import HaskStrongTypes.
Require Import HaskStrong.

CoInductive Fresh A T :=
{ next  : forall a:A, (T a * Fresh A T)
; split : Fresh A T * Fresh A T
}.

Fixpoint rawHaskTypeToWeakType (f:Fresh Kind (fun _ => WeakTypeVar))(rht:RawHaskType WeakTypeVar) {struct rht} : WeakType :=
match rht with
  | TVar    v                 => WTyVarTy v
  | TCon      tc              => WTyCon tc
  | TCoerc  t1 t2 t3          => WCoFunTy (rawHaskTypeToWeakType f t1) (rawHaskTypeToWeakType f t2) (rawHaskTypeToWeakType f t3)
  | TArrow                    => WFunTyCon
  | TApp    t1 t2             => WAppTy (rawHaskTypeToWeakType f t1) (rawHaskTypeToWeakType f t2)
  | TAll    k rht'            => let (tv,f') := next _ _ f k in WForAllTy tv (rawHaskTypeToWeakType f' (rht' tv))
  | TCode   t1 t2             => 
    match (rawHaskTypeToWeakType f t1) with
      | WTyVarTy ec => WCodeTy ec (rawHaskTypeToWeakType f t2)
      | impossible  => impossible  (* TODO: find a way to convince Coq this can't happen *)
    end
  | TFCApp    tfc tls         => WTyFunApp tfc ((fix rawHaskTypeToWeakTypeVec n v : list WeakType :=
                                                match v with
                                                  | vec_nil => nil
                                                  | a:::b   => (rawHaskTypeToWeakType f a)::(rawHaskTypeToWeakTypeVec _ b)
                                                end) _  tls)
end.


Definition typeToWeakType (f:Fresh Kind (fun _ => WeakTypeVar))
  {Γ}(τ:HaskType Γ)(φ:InstantiatedTypeEnv WeakTypeVar Γ) : WeakType :=
  rawHaskTypeToWeakType f (τ _ φ).

Variable unsafeCoerce           : WeakCoercion.
  Extract Inlined Constant unsafeCoerce => "Coercion.unsafeCoerce".

Definition strongCoercionToWeakCoercion {Γ}{Δ}(τ:HaskCoercion Γ Δ)(φ:InstantiatedTypeEnv WeakTypeVar Γ) : WeakCoercion.
  unfold HaskCoercion in τ.
  admit.
  Defined.

(* This can be used to turn HaskStrong's with arbitrary expression variables into HaskStrong's which use WeakExprVar's
 * for their variables; those can subsequently be passed to the following function (strongExprToWeakExpr) *)
(*
Definition reindexStrongExpr {VV}{HH}{eqVV:EqDecidable VV}{eqHH:EqDecidable HH}
  {Γ}{Δ}{ξ}{lev}(exp:@Expr VV eqVV Γ Δ ξ lev) : { ξ' : HH -> LeveledHaskType Γ & @Expr HH eqHH Γ Δ ξ' lev }.
  Defined.
  *)

Definition updateITE {Γ:TypeEnv}{TV:Type}(tv:TV){κ}(ite:InstantiatedTypeEnv TV Γ) : InstantiatedTypeEnv TV (κ::Γ)
  := tv:::ite.

Fixpoint strongExprToWeakExpr {Γ}{Δ}{ξ}{lev}
  (ftv:Fresh Kind                (fun _ => WeakTypeVar))
  (fcv:Fresh (WeakType*WeakType) (fun _ => WeakCoerVar))
  (exp:@Expr WeakExprVar _ Γ Δ ξ lev)
  : InstantiatedTypeEnv WeakTypeVar Γ -> WeakExpr :=
match exp as E in Expr G D X L return InstantiatedTypeEnv WeakTypeVar G -> WeakExpr with
| EVar  _ _ _ ev                => fun ite => WEVar ev
| ELit  _ _ _ lit _             => fun ite => WELit lit
| EApp  Γ' _ _ _ _ _ e1 e2      => fun ite => WEApp (strongExprToWeakExpr ftv fcv e1 ite) (strongExprToWeakExpr ftv fcv e2 ite)
| ELam  Γ' _ _ _ _ _ cv _ e     => fun ite => WELam cv (strongExprToWeakExpr ftv fcv e ite)
| ELet  Γ' _ _ _ _ _ ev e1 e2   => fun ite => WELet ev (strongExprToWeakExpr ftv fcv e1 ite) (strongExprToWeakExpr ftv fcv e2 ite)
| EEsc  Γ' _ _ ec t _ e         => fun ite => WEEsc  (ec _ ite) (strongExprToWeakExpr ftv fcv e ite) (typeToWeakType ftv t ite)
| EBrak Γ' _ _ ec t _ e         => fun ite => WEBrak (ec _ ite) (strongExprToWeakExpr ftv fcv e ite) (typeToWeakType ftv t ite)
| ECast _ _ _ γ _ τ _ _ e       => fun ite => WECast (strongExprToWeakExpr ftv fcv e ite) (strongCoercionToWeakCoercion γ ite)
| ENote _ _ _ _ n e             => fun ite => WENote n (strongExprToWeakExpr ftv fcv e ite)
| ETyApp _ _ _ _ τ _ _ _      e => fun ite => WETyApp (strongExprToWeakExpr ftv fcv e ite) (typeToWeakType ftv τ ite)
| ELetRec _ _ _ _ _ vars elrb e => fun ite => WELetRec (exprLetRec2WeakExprLetRec ftv fcv elrb ite) (strongExprToWeakExpr ftv fcv e ite)
| ECoApp _ _ γ _ _ _ _ _ _  e   => fun ite => WECoApp (strongExprToWeakExpr ftv fcv e ite) (strongCoercionToWeakCoercion γ ite)
| ECase Γ Δ ξ l   tc atypes tbranches e alts =>
  fun ite => WECase (strongExprToWeakExpr ftv fcv e ite)
    (@typeToWeakType ftv Γ tbranches ite) tc (map (fun t => typeToWeakType ftv t ite) (vec2list atypes))
    ((fix caseBranches
      (tree:Tree ??{ scb : StrongCaseBranchWithVVs _ _ tc atypes
                            & Expr (sac_Γ scb Γ)
                                   (sac_Δ scb Γ atypes (weakCK'' Δ))
                                   (update_ξ (weakLT'○ξ) (vec2list (vec_map (fun x => ((fst x),(snd x @@ weakL' l))) (scbwv_varstypes scb))))
                                   (weakLT' (tbranches@@l)) })
      : Tree ??(AltCon * list WeakTypeVar * list WeakCoerVar * list WeakExprVar * WeakExpr) :=
      match tree with
        | T_Leaf None     => []
        | T_Leaf (Some x) => let (scb,e) := x in
(*          [(sac_altcon scb,
            nil, (* FIXME *)
            nil, (* FIXME *)
            (*map (fun t => typeToWeakType ftv t ite') (vec2list (sac_types scb))*)nil, (* FIXME *)
            strongExprToWeakExpr ftv fcv e (weakITE' ite))]*) []
        | T_Branch b1 b2  => (caseBranches b1),,(caseBranches b2)
      end
    ) alts)
| ETyLam _ _ _ k _ _ e          => fun ite =>
  let (tv,ftv') := next _ _ ftv k in WETyLam tv (strongExprToWeakExpr ftv' fcv e (updateITE tv ite))
| ECoLam _ _ k _ t1 t2 _ _ _ _  e => fun ite =>
  let t1' := typeToWeakType ftv t1 ite in 
  let t2' := typeToWeakType ftv t2 ite in
  let (cv,fcv') := next _ _ fcv (t1',t2') in WECoLam cv (strongExprToWeakExpr ftv fcv' e ite)
end
with exprLetRec2WeakExprLetRec {Γ}{Δ}{ξ}{lev}{vars}
  (ftv:Fresh Kind                (fun _ => WeakTypeVar))
  (fcv:Fresh (WeakType*WeakType) (fun _ => WeakCoerVar))
  (elrb:@ELetRecBindings WeakExprVar _ Γ Δ ξ lev vars)
  : InstantiatedTypeEnv WeakTypeVar Γ -> Tree ??(WeakExprVar * WeakExpr) :=
match elrb as E in ELetRecBindings G D X L V return InstantiatedTypeEnv WeakTypeVar G -> Tree ??(WeakExprVar * WeakExpr) with
| ELR_nil    _ _ _ _           => fun ite => []
| ELR_leaf   _ _ _ _ cv v e    => fun ite => [(v,(strongExprToWeakExpr ftv fcv e ite))]
| ELR_branch _ _ _ _ _ _ b1 b2 => fun ite => (exprLetRec2WeakExprLetRec ftv fcv b1 ite),, (exprLetRec2WeakExprLetRec ftv fcv b2 ite)
end.
