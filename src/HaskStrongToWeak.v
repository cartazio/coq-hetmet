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
Require Import HaskCoreVars.
Require Import HaskCoreTypes.
Require Import HaskCore.
Require Import HaskWeakTypes.
Require Import HaskWeakVars.
Require Import HaskWeak.
Require Import HaskStrongTypes.
Require Import HaskStrong.

Fixpoint mfresh (f:Fresh Kind (fun _ => WeakTypeVar))(lk:list Kind){Γ}(ite:IList _ (fun _ => WeakTypeVar) Γ)
  : (Fresh Kind (fun _ => WeakTypeVar)) * ((vec WeakTypeVar (length lk)) * (IList _ (fun _ => WeakTypeVar) (app lk Γ))) :=
  match lk as LK return (Fresh Kind (fun _ => WeakTypeVar)) * ((vec WeakTypeVar (length LK)) *
                          (IList _ (fun _ => WeakTypeVar) (app LK Γ))) with
  | nil    => (f,(vec_nil,ite))
  | k::lk' =>
    let (f',varsite') := mfresh f lk' ite
    in  let (vars,ite') := varsite'
    in  let (v,f'') := next _ _ f' k
    in (f'',((v:::vars),v::::ite'))
  end.

Fixpoint rawHaskTypeToWeakType (f:Fresh Kind (fun _ => WeakTypeVar)){κ}(rht:RawHaskType (fun _ => WeakTypeVar) κ)
 {struct rht} : WeakType :=
match rht with
  | TVar  _  v                 => WTyVarTy v
  | TCon      tc              => WTyCon tc
  | TCoerc _ t1 t2 t3          => WCoFunTy (rawHaskTypeToWeakType f t1) (rawHaskTypeToWeakType f t2) (rawHaskTypeToWeakType f t3)
  | TArrow                    => WFunTyCon
  | TApp  _ _  t1 t2             => WAppTy (rawHaskTypeToWeakType f t1) (rawHaskTypeToWeakType f t2)
  | TAll    k rht'            => let (tv,f') := next _ _ f k in WForAllTy tv (rawHaskTypeToWeakType f' (rht' tv))
  | TCode   t1 t2             => 
    match (rawHaskTypeToWeakType f t1) with
      | WTyVarTy ec => WCodeTy ec (rawHaskTypeToWeakType f t2)
      | impossible  => impossible  (* TODO: find a way to convince Coq this can't happen *)
    end
  | TyFunApp    tfc tls         => WTyFunApp tfc (rawHaskTypeListToWeakType f tls)
end
with rawHaskTypeListToWeakType (f:Fresh Kind (fun _ => WeakTypeVar)){κ}(rht:RawHaskTypeList κ) :=
match rht with
  | TyFunApp_nil   => nil
  | TyFunApp_cons  κ kl rht' rhtl' => (rawHaskTypeToWeakType f rht')::(rawHaskTypeListToWeakType f rhtl')
end.

Definition typeToWeakType (f:Fresh Kind (fun _ => WeakTypeVar))
  {Γ}{κ}(τ:HaskType Γ κ)(φ:InstantiatedTypeEnv (fun _ => WeakTypeVar) Γ) : WeakType :=
  rawHaskTypeToWeakType f (τ _ φ).

(* This can be used to turn HaskStrong's with arbitrary expression variables into HaskStrong's which use WeakExprVar's
 * for their variables; those can subsequently be passed to the following function (strongExprToWeakExpr) *)
(*
Definition reindexStrongExpr {VV}{HH}{eqVV:EqDecidable VV}{eqHH:EqDecidable HH}
  {Γ}{Δ}{ξ}{lev}(exp:@Expr VV eqVV Γ Δ ξ lev) : { ξ' : HH -> LeveledHaskType Γ & @Expr HH eqHH Γ Δ ξ' lev }.
  Defined.
  *)

Definition updateITE {Γ:TypeEnv}{TV:Kind->Type}{κ}(tv:TV κ)(ite:InstantiatedTypeEnv TV Γ) : InstantiatedTypeEnv TV (κ::Γ)
  := tv::::ite.

Variable Prelude_error : forall {A}, string -> A.   Extract Inlined Constant Prelude_error => "Prelude.error".

Section strongExprToWeakExpr.

  Context (hetmet_brak : CoreVar).
  Context (hetmet_esc  : CoreVar).

  Fixpoint strongExprToWeakExpr {Γ}{Δ}{ξ}{τ}
    (ftv:Fresh Kind                (fun _ => WeakTypeVar))
    (fcv:Fresh (WeakType*WeakType) (fun _ => WeakCoerVar))
    (fev:Fresh WeakType            (fun _ => WeakExprVar))
    (exp:@Expr _ CoreVarEqDecidable Γ Δ ξ τ)
    : InstantiatedTypeEnv (fun _ => WeakTypeVar) Γ -> WeakExpr :=
  match exp as E in @Expr _ _ G D X L return InstantiatedTypeEnv (fun _ => WeakTypeVar) G -> WeakExpr with
  | EVar  Γ' _ ξ' ev              => fun ite => WEVar (weakExprVar ev (@typeToWeakType ftv Γ' ★  (unlev (ξ' ev)) ite))
  | ELit  _ _ _ lit _             => fun ite => WELit lit
  | EApp  Γ' _ _ _ _ _ e1 e2      => fun ite => WEApp (strongExprToWeakExpr ftv fcv fev e1 ite) (strongExprToWeakExpr ftv fcv fev e2 ite)
  | ELam  Γ'   _ _ _ t _ cv e     => fun ite => WELam (weakExprVar cv (typeToWeakType ftv t ite)) (strongExprToWeakExpr ftv fcv fev e ite)
  | ELet  Γ' _ _ t _ _ ev e1 e2   => fun ite => WELet (weakExprVar ev (typeToWeakType ftv t ite)) (strongExprToWeakExpr ftv fcv fev e1 ite) (strongExprToWeakExpr ftv fcv fev e2 ite)
  | EEsc  Γ' _ _ ec t _ e         => fun ite => WEEsc  hetmet_esc (ec _ ite) (strongExprToWeakExpr ftv fcv fev e ite) (typeToWeakType ftv t ite)
  | EBrak Γ' _ _ ec t _ e         => fun ite => WEBrak hetmet_brak (ec _ ite) (strongExprToWeakExpr ftv fcv fev e ite) (typeToWeakType ftv t ite)
  | ENote _ _ _ _ n e             => fun ite => WENote n (strongExprToWeakExpr ftv fcv fev e ite)
  | ETyApp  Γ Δ κ σ τ ξ l       e => fun ite => WETyApp (strongExprToWeakExpr ftv fcv fev e ite) (typeToWeakType ftv τ ite)
  | ELetRec _ _ _ _ _ vars elrb e => fun ite => WELetRec (exprLetRec2WeakExprLetRec ftv fcv fev elrb ite)(strongExprToWeakExpr ftv fcv fev e ite)
  | ECast Γ Δ ξ t1 t2 γ l e       => fun ite => Prelude_error "FIXME: strongExprToWeakExpr.ECast not implemented"
  | ECoApp Γ Δ κ σ₁ σ₂ γ σ ξ l e  => fun ite => Prelude_error "FIXME: strongExprToWeakExpr.ECoApp not implemented"
  | ECase Γ Δ ξ l tc tbranches atypes e alts => fun ite =>
    let (ev,fev') := next _ _ fev (typeToWeakType ftv (unlev (caseType tc atypes @@ l)) ite) in
     WECase
      ev
      (strongExprToWeakExpr ftv fcv fev' e ite)
      (@typeToWeakType ftv Γ _ tbranches ite)
      tc
      (ilist_to_list (@ilmap _ _ (fun _ => WeakType) _ (fun _ t => typeToWeakType ftv t ite) atypes))
      ((fix caseBranches
        (tree:Tree ??{ scb : StrongCaseBranchWithVVs _ _ tc atypes
                              & Expr (sac_Γ scb Γ)
                                     (sac_Δ scb Γ atypes (weakCK'' Δ))
                                     (update_ξ (weakLT'○ξ) (vec2list (vec_map
                                       (fun x => ((fst x),(snd x @@ weakL' l))) (scbwv_varstypes scb))))
                                     (weakLT' (tbranches@@l)) })
        : Tree ??(AltCon * list WeakTypeVar * list WeakCoerVar * list WeakExprVar * WeakExpr) :=
        match tree with
          | T_Leaf None     => []
          | T_Leaf (Some x) => let (scb,e) := x in
            let (ftv',evarsite') := mfresh ftv _ ite in
            let fcv' :=  fcv in
              let (evars,ite') := evarsite' in
              [(sac_altcon scb,
                vec2list evars,
                nil (*FIXME*),
                map (fun vt => weakExprVar (fst vt) (typeToWeakType ftv' (snd vt) ite')) (vec2list (scbwv_varstypes scb)),
                strongExprToWeakExpr ftv' fcv' fev' e ite'
              )]
          | T_Branch b1 b2  => (caseBranches b1),,(caseBranches b2)
        end
      ) alts)
  | ETyLam _ _ _ k _ _ e          => fun ite =>
    let (tv,ftv') := next _ _ ftv k in WETyLam tv (strongExprToWeakExpr ftv' fcv fev e (updateITE tv ite))
  | ECoLam Γ Δ κ σ σ₁ σ₂ ξ l e => fun ite =>
    let t1' := typeToWeakType ftv σ₁ ite in 
    let t2' := typeToWeakType ftv σ₂ ite in
    let (cv,fcv') := next _ _ fcv (t1',t2') in WECoLam cv (strongExprToWeakExpr ftv fcv' fev e ite)
  end
  with exprLetRec2WeakExprLetRec {Γ}{Δ}{ξ}{τ}{vars}
    (ftv:Fresh Kind                (fun _ => WeakTypeVar))
    (fcv:Fresh (WeakType*WeakType) (fun _ => WeakCoerVar))
    (fev:Fresh WeakType            (fun _ => WeakExprVar))
    (elrb:@ELetRecBindings _ CoreVarEqDecidable Γ Δ ξ τ vars)
    : InstantiatedTypeEnv (fun _ => WeakTypeVar) Γ -> Tree ??(WeakExprVar * WeakExpr) :=
  match elrb as E in ELetRecBindings G D X L V
     return InstantiatedTypeEnv (fun _ => WeakTypeVar) G -> Tree ??(WeakExprVar * WeakExpr) with
  | ELR_nil    _ _ _ _           => fun ite => []
  | ELR_leaf   _ _ ξ' cv v e    => fun ite => [((weakExprVar v (typeToWeakType ftv (unlev (ξ' v)) ite)),(strongExprToWeakExpr ftv fcv fev e ite))]
  | ELR_branch _ _ _ _ _ _ b1 b2 => fun ite => (exprLetRec2WeakExprLetRec ftv fcv fev b1 ite),, (exprLetRec2WeakExprLetRec ftv fcv fev b2 ite)
  end.
End strongExprToWeakExpr.