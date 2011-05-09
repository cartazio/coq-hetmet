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
Require Import HaskLiterals.
Require Import HaskTyCons.
Require Import HaskWeakTypes.
Require Import HaskWeakVars.
Require Import HaskWeak.
Require Import HaskWeakToCore.
Require Import HaskStrongTypes.
Require Import HaskStrong.

Section HaskStrongToWeak.

  Context (hetmet_brak : WeakExprVar).
  Context (hetmet_esc  : WeakExprVar).

  Context (mkWeakTypeVar_ : Unique -> Kind                         -> WeakTypeVar).
  Context (mkWeakCoerVar_ : Unique -> Kind -> WeakType -> WeakType -> WeakCoerVar).
  Context (mkWeakExprVar_ : Unique ->         WeakType             -> WeakExprVar).

  Definition mkWeakTypeVar (k:Kind)                 : UniqM WeakTypeVar := bind u = getU ; return mkWeakTypeVar_ u k.
  Definition mkWeakCoerVar (k:Kind)(t1 t2:WeakType) : UniqM WeakCoerVar := bind u = getU ; return mkWeakCoerVar_ u k t1 t2.
  Definition mkWeakExprVar (t:WeakType)             : UniqM WeakExprVar := bind u = getU ; return mkWeakExprVar_ u t.

  Fixpoint mfresh (lk:list Kind){Γ}(ite:IList _ (fun _ => WeakTypeVar) Γ)
    : UniqM (((vec WeakTypeVar (length lk)) * (IList _ (fun _ => WeakTypeVar) (app lk Γ)))) :=
    match lk as LK return UniqM ((vec WeakTypeVar (length LK)) * (IList _ (fun _ => WeakTypeVar) (app LK Γ))) with
    | nil    => return (vec_nil,ite)
    | k::lk' => bind v = mkWeakTypeVar k
              ; bind vars_ite' = mfresh lk' ite
              ; return ((v:::(fst vars_ite')),v::::(snd vars_ite'))
    end.

  Fixpoint rawHaskTypeToWeakType {κ}(rht:RawHaskType (fun _ => WeakTypeVar) κ) {struct rht} : UniqM WeakType :=
  match rht with
    | TVar  _  v                => return WTyVarTy v
    | TCon      tc              => return WTyCon tc
    | TCoerc _ t1 t2 t3         => bind t1' = rawHaskTypeToWeakType t1
                                 ; bind t2' = rawHaskTypeToWeakType t2
                                 ; bind t3' = rawHaskTypeToWeakType t3
                                 ; return WCoFunTy t1' t2' t3'
    | TArrow                    => return WFunTyCon
    | TApp  _ _  t1 t2          => bind t1' = rawHaskTypeToWeakType t1
                                 ; bind t2' = rawHaskTypeToWeakType t2
                                 ; return WAppTy t1' t2'
    | TAll    k rht'            => bind tv = mkWeakTypeVar k
                                 ; bind t' = rawHaskTypeToWeakType (rht' tv)
                                 ; return WForAllTy tv t'
    | TCode   t1 t2             => bind t1' = rawHaskTypeToWeakType t1
                                 ; bind t2' = rawHaskTypeToWeakType t2
                                 ; match t1' with
                                     | WTyVarTy ec => return WCodeTy ec t2'
                                     | _           => failM  "impossible"
                                   end
    | TyFunApp    tfc _ _ tls       => bind tls' = rawHaskTypeListToWeakType tls
                                 ; return WTyFunApp tfc tls'
  end
  with rawHaskTypeListToWeakType {κ}(rht:RawHaskTypeList κ) : UniqM (list WeakType) :=
  match rht with
    | TyFunApp_nil                   => return nil
    | TyFunApp_cons  κ kl rht' rhtl' => bind t  = rawHaskTypeToWeakType rht'
                                      ; bind tl = rawHaskTypeListToWeakType rhtl'
                                      ; return t::tl
  end.
  
  Definition typeToWeakType {Γ}{κ}(τ:HaskType Γ κ)(φ:InstantiatedTypeEnv (fun _ => WeakTypeVar) Γ) : UniqM WeakType :=
    rawHaskTypeToWeakType (τ _ φ).
  
  Definition updateITE {Γ:TypeEnv}{TV:Kind->Type}{κ}(tv:TV κ)(ite:InstantiatedTypeEnv TV Γ) : InstantiatedTypeEnv TV (κ::Γ)
    := tv::::ite.
  
  Definition coercionToWeakCoercion Γ Δ κ t1 t2 ite (γ:@HaskCoercion Γ Δ (@mkHaskCoercionKind Γ κ t1 t2))
    : UniqM WeakCoercion
    := bind t1' = @typeToWeakType Γ κ t1 ite
     ; bind t2' = @typeToWeakType Γ κ t2 ite
     ; return WCoUnsafe t1' t2'.
  
  Fixpoint seqM {a}(l:list (UniqM a)) : UniqM (list a) :=
    match l with
      | nil  => return nil
      | x::y => bind x' = x
              ; bind y' = seqM y
              ; return x'::y'
    end.
  
  Context {VV}{eqVV:EqDecidable VV}{toStringVV:ToString VV}.
  
  Definition update_χ (χ:VV->???WeakExprVar)(vv:VV)(ev':WeakExprVar) : VV->???WeakExprVar :=
    fun vv' =>
      if eqd_dec vv vv'
      then OK ev'
      else χ vv'.

  Fixpoint update_χ' (χ:VV->???WeakExprVar)(varsexprs:list (VV * WeakExprVar)) : VV->???WeakExprVar :=
    match varsexprs with
      | nil => χ
      | (vv,wev)::rest => update_χ (update_χ' χ rest) vv wev
    end.

  Fixpoint exprToWeakExpr {Γ}{Δ}{ξ}{τ}(χ:VV->???WeakExprVar)(exp:@Expr _ eqVV Γ Δ ξ τ)
    : InstantiatedTypeEnv (fun _ => WeakTypeVar) Γ
    -> UniqM WeakExpr :=
    match exp as E in @Expr _ _ G D X L return InstantiatedTypeEnv (fun _ => WeakTypeVar) G -> UniqM WeakExpr with
    | EVar  Γ' _ ξ' ev              => fun ite => match χ ev with OK v => return WEVar v | Error s => failM s end
    | EGlobal Γ' _ ξ'   g v lev     => fun ite => bind tv' = mapM (ilist_to_list (ilmap (fun κ x => typeToWeakType x ite) v))
                                                ; return (fold_left (fun x y => WETyApp x y) tv' (WEVar g))
    | ELam  Γ'   _ _ tv _ _ cv e    => fun ite => bind tv' = typeToWeakType tv ite
                                                ; bind ev' = mkWeakExprVar tv'
                                                ; bind e'  = exprToWeakExpr (update_χ χ cv ev') e ite
                                                ; return WELam ev' e'
    | ELet  Γ' _ _ t _ _ ev e1 e2   => fun ite => bind tv' = typeToWeakType t ite
                                                ; bind e1' = exprToWeakExpr χ e1 ite
                                                ; bind ev' = mkWeakExprVar tv'
                                                ; bind e2' = exprToWeakExpr (update_χ χ ev ev') e2 ite
                                                ; return WELet ev' e1' e2'
    | ELit  _ _ _ lit _             => fun ite => return WELit lit
    | EApp  Γ' _ _ _ _ _ e1 e2      => fun ite => bind e1' = exprToWeakExpr χ e1 ite
                                                ; bind e2' = exprToWeakExpr χ e2 ite
                                                ; return WEApp e1' e2'
    | EEsc  Γ' _ _ ec t _ e         => fun ite => bind t' = typeToWeakType t ite
                                                ; bind e' = exprToWeakExpr χ e ite
                                                ; return WEEsc hetmet_esc (ec _ ite) e' t'
    | EBrak Γ' _ _ ec t _ e         => fun ite => bind t' = typeToWeakType t ite
                                                ; bind e' = exprToWeakExpr χ e ite
                                                ; return WEBrak hetmet_brak (ec _ ite) e' t'
    | ENote _ _ _ _ n e             => fun ite => bind e' = exprToWeakExpr χ e ite
                                                ; return WENote n e'
    | ETyApp  Γ Δ κ σ τ ξ l       e => fun ite => bind t' = typeToWeakType τ ite
                                                ; bind e' = exprToWeakExpr χ e ite
                                                ; return WETyApp e' t'
    | ECoApp Γ Δ κ σ₁ σ₂ γ σ ξ l e  => fun ite => bind e' = exprToWeakExpr χ e ite
                                                ; bind c' = coercionToWeakCoercion _ _ _ _ _ ite γ
                                                ; return WECoApp e' c'
    | ECast Γ Δ ξ t1 t2 γ l e      => fun ite  => bind e' = exprToWeakExpr χ e ite
                                                ; bind c' = coercionToWeakCoercion _ _ _ _ _ ite γ
                                                ; return WECast e' c'
    | ETyLam _ _ _ k _ _ e          => fun ite => bind tv = mkWeakTypeVar k
                                                ; bind e' = exprToWeakExpr χ e (updateITE tv ite)
                                                ; return WETyLam tv e'
    | ECoLam Γ Δ κ σ σ₁ σ₂ ξ l e    => fun ite => bind t1' = typeToWeakType σ₁ ite
                                                ; bind t2' = typeToWeakType σ₂ ite
                                                ; bind cv  = mkWeakCoerVar κ t1' t2'
                                                ; bind e'  = exprToWeakExpr χ e ite
                                                ; return WECoLam cv e'
    | ECase Γ Δ ξ l tc tbranches atypes escrut alts => 
         fun ite => bind tscrut'    = typeToWeakType (caseType tc atypes) ite
                  ; bind vscrut'    = mkWeakExprVar tscrut'
                  ; bind tbranches' = @typeToWeakType Γ _ tbranches ite
                  ; bind escrut'    = exprToWeakExpr χ escrut ite
                  ; bind branches'  =
                      ((fix caseBranches (tree:Tree ??{sac : _ & { scb : StrongCaseBranchWithVVs VV _ _ _ sac & Expr _ _ _ _ } })
                            : UniqM (Tree ??(WeakAltCon*list WeakTypeVar*list WeakCoerVar*list WeakExprVar*WeakExpr)) :=
                            match tree with
                              | T_Leaf None           => return []
                              | T_Leaf (Some x)       =>
                                let (sac,scb_e) := x in
                                let (scb,e) := scb_e in
                                let varstypes := vec2list (scbwv_varstypes scb) in
                                      bind evars_ite = mfresh _ ite
                                    ; bind exprvars  = seqM (map (fun vt:VV * HaskType _ ★
                                                                        => bind tleaf = typeToWeakType (snd vt) (snd evars_ite)
                                                                         ; bind v' = mkWeakExprVar tleaf
                                                                         ; return ((fst vt),v'))
                                                                varstypes)
                                    ; let χ' := update_χ' χ exprvars in
                                      bind e'' = exprToWeakExpr χ' e (snd evars_ite)
                                    ; return [(sac_altcon sac, vec2list (fst evars_ite), nil, (map (@snd _ _) exprvars), e'')]
                              | T_Branch b1 b2        => bind b1' = caseBranches b1
                                                       ; bind b2' = caseBranches b2
                                                       ; return (b1',,b2')
                            end) alts)
                  ; bind tys = seqM (ilist_to_list (@ilmap _ _
                                  (fun _ => UniqM WeakType) _ (fun _ t => typeToWeakType t ite) atypes))
                  ; return WECase vscrut' escrut' tbranches' tc tys branches'

    | ELetRec _ _ _ _ _ vars disti elrb e => fun ite => bind vars' = seqM (map (fun vt:VV * HaskType _ ★
                                                                        => bind tleaf = typeToWeakType (snd vt) ite
                                                                         ; bind v' = mkWeakExprVar tleaf
                                                                         ; return ((fst vt),v'))
                                                                (leaves vars))
                                                ; let χ' := update_χ' χ vars' in
                                                  bind elrb' = exprLetRec2WeakExprLetRec χ' elrb ite
                                                ; bind e'    = exprToWeakExpr χ' e ite
                                                ; return WELetRec elrb' e'
    end
    with exprLetRec2WeakExprLetRec  {Γ}{Δ}{ξ}{τ}(χ:VV->???WeakExprVar){vars}(elrb:@ELetRecBindings _ eqVV Γ Δ ξ τ vars)
      : InstantiatedTypeEnv (fun _ => WeakTypeVar) Γ -> UniqM (Tree ??(WeakExprVar * WeakExpr)) :=
    match elrb as E in ELetRecBindings G D X L V
       return InstantiatedTypeEnv (fun _ => WeakTypeVar) G -> UniqM (Tree ??(WeakExprVar * WeakExpr)) with
    | ELR_nil    _ _ _ _           => fun ite => return []
    | ELR_leaf   _ _ ξ' cv v t e   => fun ite => bind t'  = typeToWeakType t ite
                                               ; bind e'  = exprToWeakExpr χ e ite
                                               ; bind v'  = match χ v with Error s => failM s | OK y => return y end
                                               ; return [(v',e')]
    | ELR_branch _ _ _ _ _ _ b1 b2 => fun ite => bind b1' = exprLetRec2WeakExprLetRec χ b1 ite
                                               ; bind b2' = exprLetRec2WeakExprLetRec χ b2 ite
                                               ; return b1',,b2'
  end.


  Fixpoint strongExprToWeakExpr (us:UniqSupply){Γ}{Δ}{ξ}{τ}(exp:@Expr _ eqVV Γ Δ ξ τ)
    (ite:InstantiatedTypeEnv (fun _ => WeakTypeVar) Γ)
    : ???WeakExpr :=
    match exprToWeakExpr (fun v => Error ("unbound variable " +++ toString v)) exp ite with
      uniqM f => f us >>= fun x => OK (snd x)
      end.

End HaskStrongToWeak.
