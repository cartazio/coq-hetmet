(*********************************************************************************************************************************)
(* HaskWeakToStrong: convert HaskWeak to HaskStrong                                                                              *)
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
Require Import HaskCoreTypes.
Require Import HaskCoreVars.

Open Scope string_scope.
Definition TyVarResolver Γ   := forall wt:WeakTypeVar, HaskTyVar Γ wt.
Definition CoVarResolver Γ Δ := forall wt:WeakCoerVar, HaskCoVar Γ Δ.

Definition upφ {Γ}(tv:WeakTypeVar)(φ:TyVarResolver Γ) : TyVarResolver ((tv:Kind)::Γ).
  unfold TyVarResolver.
  refine (fun tv' =>
    if eqd_dec tv tv' 
    then let fresh := @FreshHaskTyVar Γ tv in _
    else fun TV ite => φ tv' TV (weakITE ite)).
  rewrite <- _H; apply fresh.
  Defined.

Definition upφ' {Γ}(tvs:list WeakTypeVar)(φ:TyVarResolver Γ)
  : (TyVarResolver (app (map (fun tv:WeakTypeVar => tv:Kind) tvs) Γ)).
  induction tvs.
  apply φ.    
  simpl.
  apply upφ.
  apply IHtvs.
  Defined.

Definition substPhi {Γ:TypeEnv}(κ κ':Kind)(θ:HaskType Γ κ) : HaskType (κ::Γ) κ' -> HaskType Γ κ'.
  intro ht.
  refine (substT _ θ).
  clear θ.
  unfold HaskType in ht.
  intros.
  apply ht.
  apply ICons; [ idtac | apply env ].
  apply X.
  Defined.

Definition substφ {Γ:TypeEnv}(lk:list Kind)(θ:IList _ (fun κ => HaskType Γ κ) lk){κ} : HaskType (app lk Γ) κ -> HaskType Γ κ.
  induction lk.
  intro q; apply q.
  simpl.
  intro q.
  apply IHlk.
  inversion θ; subst; auto.
  inversion θ; subst.
  eapply substPhi.
  eapply weakT'.
  apply X.
  apply q.
  Defined.

(* this is a StrongAltCon plus some stuff we know about StrongAltCons which we've built ourselves *)
Record StrongAltConPlusJunk {tc:TyCon} :=
{ sacpj_sac : @StrongAltCon tc
; sacpj_φ   : forall Γ          (φ:TyVarResolver Γ  ),  (TyVarResolver (sac_Γ sacpj_sac Γ))
; sacpj_ψ   : forall Γ Δ atypes (ψ:WeakCoerVar -> HaskCoVar Γ Δ),
                (WeakCoerVar -> HaskCoVar _ (sac_Δ sacpj_sac Γ atypes (weakCK'' Δ)))
}.
Implicit Arguments StrongAltConPlusJunk [ ].
Coercion sacpj_sac : StrongAltConPlusJunk >-> StrongAltCon. 

(* yes, I know, this is really clumsy *)
Variable emptyφ : TyVarResolver nil.
  Extract Inlined Constant emptyφ => "(\x -> Prelude.error ""encountered unbound tyvar!"")".

Definition mkPhi (lv:list WeakTypeVar)
  : (TyVarResolver (map (fun x:WeakTypeVar => x:Kind) lv)).
  set (upφ'(Γ:=nil) lv emptyφ) as φ'.
  rewrite <- app_nil_end in φ'.
  apply φ'.
  Defined.

Definition dataConExKinds dc := vec_map (fun x:WeakTypeVar => (x:Kind)) (list2vec (dataConExTyVars dc)).
Definition tyConKinds     tc := vec_map (fun x:WeakTypeVar => (x:Kind)) (list2vec (tyConTyVars tc)).

Definition fixkind {κ}(tv:WeakTypeVar) := weakTypeVar tv κ.
Notation " ` x " := (@fixkind _ x) (at level 100).

Ltac matchThings T1 T2 S :=
  destruct (eqd_dec T1 T2) as [matchTypeVars_pf|];
   [ idtac | apply (Error (S +++ T1 +++ " " +++ T2)) ].

Definition mkTAll' {κ}{Γ} : HaskType (κ :: Γ) ★ -> (forall TV (ite:InstantiatedTypeEnv TV Γ), TV κ -> RawHaskType TV ★).
  intros.
  unfold InstantiatedTypeEnv in ite.
  apply X.
  apply (X0::::ite).
  Defined.

Definition mkTAll {κ}{Γ} : HaskType (κ :: Γ) ★ -> HaskType Γ ★.
  intro.
  unfold HaskType.
  intros.
  apply (TAll κ).
  eapply mkTAll'.
  apply X.
  apply X0.
  Defined.

Definition weakTypeToType : forall {Γ:TypeEnv}(φ:TyVarResolver Γ)(t:WeakType), ???(HaskTypeOfSomeKind Γ).
  refine (fix weakTypeToType {Γ:TypeEnv}(φ:TyVarResolver Γ)(t:WeakType) {struct t} : ???(HaskTypeOfSomeKind Γ) :=
  match t with
    | WFunTyCon         => let case_WFunTyCon := tt in OK (haskTypeOfSomeKind (fun TV ite => TArrow))
    | WTyCon      tc    => let case_WTyCon := tt    in _
    | WClassP   c lt    => let case_WClassP := tt   in Error "weakTypeToType: WClassP not implemented"
    | WIParam _ ty      => let case_WIParam := tt   in Error "weakTypeToType: WIParam not implemented"
    | WAppTy  t1 t2     => let case_WAppTy := tt    in weakTypeToType _ φ t1 >>= fun t1' => weakTypeToType _ φ t2 >>= fun t2' => _
    | WTyVarTy  v       => let case_WTyVarTy := tt  in _
    | WForAllTy wtv t   => let case_WForAllTy := tt in weakTypeToType _ (upφ wtv φ) t >>= fun t => _
    | WCodeTy ec tbody  => let case_WCodeTy := tt   in weakTypeToType _ φ tbody >>= fun tbody' => _
    | WCoFunTy t1 t2 t3 => let case_WCoFunTy := tt  in
      weakTypeToType _ φ t1 >>= fun t1' =>
      weakTypeToType _ φ t2 >>= fun t2' =>
      weakTypeToType _ φ t3 >>= fun t3' => _
    | WTyFunApp   tc lt =>
      ((fix weakTypeListToTypeList (lk:list Kind) (lt:list WeakType)
        { struct lt } : ???(forall TV (ite:InstantiatedTypeEnv TV Γ), @RawHaskTypeList TV lk) :=
        match lt with
          | nil    => match lk as LK return ???(forall TV (ite:InstantiatedTypeEnv TV Γ), @RawHaskTypeList TV LK) with
                        | nil => OK (fun TV _ => TyFunApp_nil)
                        | _   => Error "WTyFunApp not applied to enough types"
                      end
          | tx::lt' => weakTypeToType Γ φ tx >>= fun t' =>
                        match lk as LK return ???(forall TV (ite:InstantiatedTypeEnv TV Γ), @RawHaskTypeList TV LK) with
                          | nil    => Error "WTyFunApp applied to too many types"
                          | k::lk' => weakTypeListToTypeList lk' lt' >>= fun rhtl' =>
                                        let case_weakTypeListToTypeList := tt in _
                        end
        end
      ) (fst (tyFunKind tc)) lt) >>= fun lt' => let case_WTyFunApp := tt in  _
  end ); clear weakTypeToType.

  destruct case_WTyVarTy.
    apply OK.
    exact (haskTypeOfSomeKind (fun TV env => TVar (φ v TV env))).

  destruct case_WAppTy.
    destruct t1' as  [k1' t1'].
    destruct t2' as [k2' t2'].
    destruct k1';
      try (matchThings k1'1 k2' "Kind mismatch in WAppTy: ";
        subst; apply OK; apply (haskTypeOfSomeKind (fun TV env => TApp (t1' TV env) (t2' TV env))));
      apply (Error "Kind mismatch in WAppTy:: ").
   
  destruct case_weakTypeListToTypeList.
    destruct t' as [ k' t' ].
    matchThings k k' "Kind mismatch in weakTypeListToTypeList".
    subst.
    apply (OK (fun TV ite => TyFunApp_cons _ _ (t' TV ite) (rhtl' TV ite))).

  destruct case_WTyFunApp.
    apply OK.
    eapply haskTypeOfSomeKind.
    unfold HaskType; intros.
    apply TyFunApp.
    apply lt'.
    apply X.

  destruct case_WTyCon.
    apply OK.
    eapply haskTypeOfSomeKind.
    unfold HaskType; intros.
    apply (TCon tc).

  destruct case_WCodeTy.    
    destruct tbody'.
    matchThings κ ★ "Kind mismatch in WCodeTy: ".
    apply OK.
    eapply haskTypeOfSomeKind.
    unfold HaskType; intros.
    apply TCode.
    apply (TVar (φ (@fixkind ★ ec) TV X)).
    subst.
    apply h.
    apply X.

  destruct case_WCoFunTy.
    destruct t1' as [ k1' t1' ].
    destruct t2' as [ k2' t2' ].
    destruct t3' as [ k3' t3' ].
    matchThings k1' k2' "Kind mismatch in arguments of WCoFunTy".
    subst.
    matchThings k3' ★ "Kind mismatch in result of WCoFunTy".
    subst.
    apply OK.
    apply (haskTypeOfSomeKind (t1' ∼∼ t2' ⇒ t3')).

  destruct case_WForAllTy.
    destruct t1.
    matchThings ★  κ "Kind mismatch in WForAllTy: ".
    subst.
    apply OK.
    apply (@haskTypeOfSomeKind _ ★).
    apply (@mkTAll wtv).
    apply h.
    Defined.
    


(* information about a datacon/literal/default which is common to all instances of a branch with that tag *)
Section StrongAltCon.
  Context (tc : TyCon)(dc:DataCon tc).
(*
Definition weakTypeToType' {Γ} : vec (HaskType Γ) tc -> WeakType → HaskType (app (vec2list (dataConExKinds dc)) Γ).
  intro avars.
  intro ct.
  set (vec_map (@weakT' _ (vec2list (dataConExKinds dc))) avars) as avars'.
  set (@substφ _ _ avars') as q.
  set (upφ' (tyConTyVars tc)  (mkPhi (dataConExTyVars dc))) as φ'.
  set (@weakTypeToType _ φ' ct) as t.
  set (@weakT'' _ Γ t) as t'.
  set (@lamer _ _ _ t') as t''.
  fold (tyConKinds tc) in t''.
  fold (dataConExKinds dc) in t''.
  apply (q (tyConKinds tc)).
  unfold tyConKinds.
  unfold dataConExKinds.
  rewrite <- vec2list_map_list2vec.
  rewrite <- vec2list_map_list2vec.
  rewrite vec2list_list2vec.
  rewrite vec2list_list2vec.
  apply t''.
  Defined.

Definition mkStrongAltCon : @StrongAltCon tc.
  refine
   {| sac_altcon      := DataAlt dc
    ; sac_numCoerVars := length (dataConCoerKinds dc)
    ; sac_numExprVars := length (dataConFieldTypes dc)
    ; sac_akinds      := tyConKinds tc
    ; sac_ekinds      := dataConExKinds dc
    ; sac_coercions   := fun Γ avars => let case_sac_coercions := tt in _
    ; sac_types       := fun Γ avars => let case_sac_types := tt in _
    |}.
  
  destruct case_sac_coercions.
    refine (vec_map _ (list2vec (dataConCoerKinds dc))).
    intro.
    destruct X.
    apply (mkHaskCoercionKind (weakTypeToType' avars w) (weakTypeToType' avars w0)).

  destruct case_sac_types.
    refine (vec_map _ (list2vec (dataConFieldTypes dc))).
    intro X.
    apply (weakTypeToType' avars).
    apply X.
    Defined.
 
Lemma weakCV' : forall {Γ}{Δ} Γ',
   HaskCoVar Γ Δ
   -> HaskCoVar (app Γ' Γ) (weakCK'' Δ).
  intros.
  unfold HaskCoVar in *.
  intros; apply (X TV CV).
  apply vec_chop' in env; auto.
  unfold InstantiatedCoercionEnv in *.
  unfold weakCK'' in cenv.
  destruct Γ'.
  apply cenv.
  rewrite <- map_preserves_length in cenv.
  apply cenv.
  Defined.

Definition mkStrongAltConPlusJunk : StrongAltConPlusJunk tc.
    refine 
     {| sacpj_sac     := mkStrongAltCon
      ; sacpj_φ       := fun Γ φ => (fun htv => weakV' (φ htv))
      ; sacpj_ψ       := fun Γ Δ avars ψ => (fun htv => _ (weakCV' (vec2list (sac_ekinds mkStrongAltCon)) (ψ htv)))
      |}.
    intro.
    unfold sac_Γ.
    unfold HaskCoVar in *.
    intros.
    apply (x TV CV env).
    simpl in cenv.
    unfold sac_Δ in *.
    unfold InstantiatedCoercionEnv in *.
    apply vec_chop' in cenv.
    apply cenv.
    Defined.
*)
End StrongAltCon.
(*
Definition mkStrongAltConPlusJunk' (tc : TyCon)(alt:AltCon) : ???(@StrongAltConPlusJunk tc).
  destruct alt.
  set (c:DataCon _) as dc.
  set ((dataConTyCon c):TyCon) as tc' in *.
  set (eqd_dec tc tc') as eqpf; destruct eqpf;
    [ idtac
      | apply (Error ("in a case of tycon "+++tc+++", found a branch with datacon "+++dc)) ]; subst.
  apply OK.
  eapply mkStrongAltConPlusJunk.
  simpl in *.
  apply dc.

  apply OK; refine {| sacpj_sac := {| sac_akinds  := tyConKinds tc
                    ; sac_ekinds  := vec_nil ; sac_coercions := fun _ _ => vec_nil ; sac_types := fun _ _ => vec_nil
                    ; sac_altcon := LitAlt h
                    |} |}.
            intro; intro φ; apply φ.
            intro; intro; intro; intro ψ; apply ψ.
  apply OK; refine {| sacpj_sac := {| sac_akinds  := tyConKinds tc
                    ; sac_ekinds := vec_nil ; sac_coercions := fun _ _ => vec_nil ; sac_types := fun _ _ => vec_nil
                      ; sac_altcon := DEFAULT |} |}.
            intro; intro φ; apply φ.
            intro; intro; intro; intro ψ; apply ψ.
Defined.
Fixpoint mLetRecTypesVars {Γ} (mlr:Tree ??(WeakExprVar * WeakExpr)) φ : Tree ??(WeakExprVar * HaskType Γ ★) :=
  match mlr with
  | T_Leaf None                         => []
  | T_Leaf (Some ((weakExprVar v t),e)) => [((weakExprVar v t),weakTypeToType φ t)]
  | T_Branch b1 b2                      => ((mLetRecTypesVars b1 φ),,(mLetRecTypesVars b2 φ))
  end.
*)


Definition weakExprVarToWeakType : WeakExprVar -> WeakType :=
  fun wev => match wev with weakExprVar _ t => t end.
  Coercion weakExprVarToWeakType : WeakExprVar >-> WeakType.

(*Variable weakCoercionToHaskCoercion : forall Γ Δ κ, WeakCoercion -> HaskCoercion Γ Δ κ.*)

Definition weakψ {Γ}{Δ:CoercionEnv Γ} {κ}(ψ:WeakCoerVar -> HaskCoVar Γ Δ) :
  WeakCoerVar -> HaskCoVar Γ (κ::Δ).
  intros.
  unfold HaskCoVar.
  intros.
  apply (ψ X TV CV env).
  inversion cenv; auto.
  Defined.

(* attempt to "cast" an expression by simply checking if it already had the desired type, and failing otherwise *)
Definition castExpr (err_msg:string) {Γ} {Δ} {ξ} {τ} τ' (e:@Expr _ WeakExprVarEqDecidable Γ Δ ξ τ)
  : ???(@Expr _ WeakExprVarEqDecidable Γ Δ ξ τ').
  intros.
  destruct τ  as [τ  l].
  destruct τ' as [τ' l'].
  destruct (eqd_dec l l'); [ idtac | apply (Error ("level mismatch in castExpr: "+++err_msg)) ].
  destruct (eqd_dec τ τ'); [ idtac | apply (Error ("type mismatch in castExpr: " +++err_msg+++" "+++τ+++" and "+++τ')) ].
  subst.
  apply OK.
  apply e.
  Defined.

Definition weakTypeToType' : forall {Γ:TypeEnv}(φ:TyVarResolver Γ)(t:WeakType) κ, ???(HaskType Γ κ).
  intros.
  set (weakTypeToType φ t) as wt.
  destruct wt; try apply (Error error_message).
  destruct h.
  matchThings κ κ0 "Kind mismatch in weakTypeToType': ".
  subst.
  apply OK.
  apply h.
  Defined.

Definition weakExprToStrongExpr : forall
    (Γ:TypeEnv)
    (Δ:CoercionEnv Γ)
    (φ:TyVarResolver Γ)
    (ψ:CoVarResolver Γ Δ)
    (ξ:WeakExprVar -> LeveledHaskType Γ ★)
    (τ:HaskType Γ ★)
    (lev:HaskLevel Γ),
    WeakExpr -> ???(Expr Γ Δ ξ (τ @@ lev) ).
  refine ((
    fix weakExprToStrongExpr 
    (Γ:TypeEnv)
    (Δ:CoercionEnv Γ)
    (φ:TyVarResolver Γ)
    (ψ:CoVarResolver Γ Δ)
    (ξ:WeakExprVar -> LeveledHaskType Γ ★)
    (τ:HaskType Γ ★)
    (lev:HaskLevel Γ)
    (we:WeakExpr) : ???(@Expr _ WeakExprVarEqDecidable Γ Δ ξ (τ @@ lev) )  :=
    match we with

    | WEVar   v                         => castExpr "WEVar" (τ @@ lev) (EVar Γ Δ ξ v)

    | WELit   lit                       => castExpr "WELit" (τ @@ lev) (ELit Γ Δ ξ lit lev)

    | WELam   ev e                      => weakTypeToType' φ ev ★ >>= fun tv =>
                                             weakTypeOfWeakExpr e >>= fun t =>
                                               weakTypeToType' φ t ★ >>= fun τ' =>
                                                 weakExprToStrongExpr Γ Δ φ ψ (update_ξ ξ ((ev,tv@@lev)::nil)) τ' _ e >>= fun e' =>
                                                   castExpr "WELam" _ (ELam Γ Δ ξ tv _ _ ev e')

    | WEBrak  ec e tbody                => weakExprToStrongExpr Γ Δ φ ψ ξ τ ((φ (`ec))::lev) e >>= fun e' =>
                                             castExpr "WEBrak" _ (EBrak _ _ _ (φ (`ec)) _ lev e')

    | WEEsc   ec e tbody                => weakTypeToType' φ tbody ★ >>= fun tbody' =>
                                           match lev with
                                             | nil       => Error "ill-leveled escapification"
                                             | ec'::lev' => weakExprToStrongExpr Γ Δ φ ψ ξ (<[ φ (`ec) |- tbody' ]>) lev e
                                               >>= fun e' =>
                                                              castExpr "WEEsc" (τ@@lev) (EEsc _ _ _ (φ (`ec)) _ lev e')
                                           end
    | WENote  n e                       => weakExprToStrongExpr Γ Δ φ ψ ξ τ lev e >>= fun e' => OK (ENote _ _ _ _ n e')

    | WELet   v ve  ebody               => weakTypeToType' φ v ★  >>= fun tv =>
                                             weakExprToStrongExpr Γ Δ φ ψ ξ tv lev ve >>= fun ve' =>
                                               weakExprToStrongExpr Γ Δ φ ψ (update_ξ ξ ((v,tv@@lev)::nil)) τ lev ebody
                                               >>= fun ebody' =>
                                                 OK (ELet _ _ _ tv _ lev v ve' ebody')

    | WEApp   e1 e2                     => weakTypeOfWeakExpr e2 >>= fun t2 =>
                                             weakTypeToType' φ t2 ★ >>= fun t2' =>
                                               weakExprToStrongExpr Γ Δ φ ψ ξ t2' lev e2 >>= fun e2' =>
                                                 weakExprToStrongExpr Γ Δ φ ψ ξ (t2'--->τ) lev e1 >>= fun e1' =>
                                                   OK (EApp _ _ _ _ _ _ e1' e2')

    | WETyLam tv e                      => let φ' := upφ tv φ in
                                             weakTypeOfWeakExpr e >>= fun te =>
                                               weakTypeToType' φ' te ★ >>= fun τ' =>
                                                 weakExprToStrongExpr _ (weakCE Δ) φ' (weakCV○ψ) (weakLT○ξ) τ' (weakL lev) e
                                                 >>= fun e' =>
                                                   castExpr "WETyLam1" _ e' >>= fun e'' =>
                                                     castExpr "WETyLam2" _ (ETyLam Γ Δ ξ tv (mkTAll' τ') lev e'')

    | WETyApp e t                       => weakTypeOfWeakExpr e >>= fun te =>
                                           match te with
                                             | WForAllTy wtv te' =>
                                               let φ' := upφ wtv φ in
                                                 weakTypeToType' φ' te' ★ >>= fun te'' =>
                                                   weakExprToStrongExpr Γ Δ φ ψ ξ (mkTAll te'') lev e >>= fun e' =>
                                                     weakTypeToType' φ t wtv >>= fun t' =>
                                                       castExpr "WETyApp" _ (ETyApp Γ Δ wtv (mkTAll' te'') t' ξ lev e')
                                             | _                 => Error ("weakTypeToType: WETyApp body with type "+++te)
                                           end

    (* I had all of these working before I switched to a Kind-indexed representation for types; it will take a day or two
     * to get them back working again *)
    | WECoApp e t                       => Error "weakExprToStrongExpr: WECoApp  not yet implemented"
    | WECoLam cv e                      => Error "weakExprToStrongExpr: WECoLam  not yet implemented"
    | WECast  e co                      => Error "weakExprToStrongExpr: WECast   not yet implemented"
    | WELetRec rb   e                   => Error "weakExprToStrongExpr: WELetRec not yet implemented"
    | WECase  e tbranches tc avars alts => Error "weakExprToStrongExpr: WECase   not yet implemented"
    end)).
    Defined.

