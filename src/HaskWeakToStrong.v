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

Definition upφ {Γ}(tv:WeakTypeVar)(φ:WeakTypeVar -> HaskTyVar Γ) : (WeakTypeVar -> HaskTyVar ((tv:Kind)::Γ)) :=
  fun tv' =>
    if eqd_dec tv tv' 
    then FreshHaskTyVar (tv:Kind)
    else fun TV ite => φ tv' TV (weakITE ite).



Definition upφ' {Γ}(tvs:list WeakTypeVar)(φ:WeakTypeVar -> HaskTyVar Γ)
  : (WeakTypeVar -> HaskTyVar (app (map (fun tv:WeakTypeVar => tv:Kind) tvs) Γ)).
  induction tvs.
  apply φ.    
  simpl.
  apply upφ.
  apply IHtvs.
  Defined.

Open Scope string_scope.

Fixpoint weakTypeToType {Γ:TypeEnv}(φ:WeakTypeVar -> HaskTyVar Γ)(t:WeakType) : HaskType Γ :=
    match t with
      | WTyVarTy  v       => fun TV env => @TVar TV (φ v TV env)
      | WCoFunTy t1 t2 t3 => (weakTypeToType φ t1) ∼∼ (weakTypeToType φ t2) ⇒ (weakTypeToType φ t3)
      | WFunTyCon         => fun TV env => TArrow
      | WTyCon      tc    => fun TV env => TCon tc
      | WTyFunApp   tc lt => fun TV env => fold_left TApp (map (fun t => weakTypeToType φ t TV env) lt) (TCon tc) (* FIXME *)
      | WClassP   c lt    => fun TV env => fold_left TApp (map (fun t=> weakTypeToType φ t TV env) lt) (TCon (classTyCon c))
      | WIParam _ ty      => weakTypeToType φ ty
      | WForAllTy wtv t   => (fun TV env => TAll (wtv:Kind) (fun tv => weakTypeToType (@upφ Γ wtv φ) t TV (tv:::env)))
      | WAppTy  t1 t2     => fun TV env => TApp (weakTypeToType φ t1 TV env) (weakTypeToType φ t2 TV env)
      | WCodeTy ec tbody  => fun TV env => TCode (TVar (φ ec TV env)) (weakTypeToType φ tbody TV env)
    end.


Definition substPhi0 {Γ:TypeEnv}(κ:Kind)(θ:HaskType Γ) : HaskType (κ::Γ) -> HaskType Γ.
  intro ht.
  refine (substT _ θ).
  clear θ.
  unfold HaskType in ht.
  intros.
  apply ht.
  apply vec_cons; [ idtac | apply env ].
  apply X.
  Defined.

Definition substPhi {Γ:TypeEnv}(κ:list Kind)(θ:vec (HaskType Γ) (length κ)) : HaskType (app κ Γ) -> HaskType Γ.
  induction κ.
  intro q; apply q.
  simpl.
  intro q.
  apply IHκ.
  inversion θ; subst; auto.
  inversion θ; subst.
  apply (substPhi0 _ (weakT' X) q).
  Defined.

Definition substφ {Γ}{n}(ltypes:vec (HaskType Γ) n)(Γ':vec _ n)(ht:HaskType (app (vec2list Γ') Γ)) : HaskType Γ.
  apply (@substPhi Γ (vec2list Γ')).
  rewrite vec2list_len.
  apply ltypes.
  apply ht.
  Defined.

(* this is a StrongAltCon plus some stuff we know about StrongAltCons which we've built ourselves *)
Record StrongAltConPlusJunk {tc:TyCon} :=
{ sacpj_sac : @StrongAltCon tc
; sacpj_φ   : forall Γ          (φ:WeakTypeVar -> HaskTyVar Γ  ),  (WeakTypeVar -> HaskTyVar (sac_Γ sacpj_sac Γ))
; sacpj_ψ   : forall Γ Δ atypes (ψ:WeakCoerVar -> HaskCoVar Γ Δ),
                (WeakCoerVar -> HaskCoVar _ (sac_Δ sacpj_sac Γ atypes (weakCK'' Δ)))
}.
Implicit Arguments StrongAltConPlusJunk [ ].
Coercion sacpj_sac : StrongAltConPlusJunk >-> StrongAltCon. 

(* yes, I know, this is really clumsy *)
Variable emptyφ : WeakTypeVar -> HaskTyVar nil.
  Extract Inlined Constant emptyφ => "(\x -> Prelude.error ""encountered unbound tyvar!"")".

Definition mkPhi (lv:list WeakTypeVar)
  : (WeakTypeVar -> HaskTyVar (map (fun x:WeakTypeVar => x:Kind) lv)).
  set (upφ'(Γ:=nil) lv emptyφ) as φ'.
  rewrite <- app_nil_end in φ'.
  apply φ'.
  Defined.

Definition dataConExKinds dc := vec_map (fun x:WeakTypeVar => (x:Kind)) (list2vec (dataConExTyVars dc)).
Definition tyConKinds     tc := vec_map (fun x:WeakTypeVar => (x:Kind)) (list2vec (tyConTyVars tc)).

(* information about a datacon/literal/default which is common to all instances of a branch with that tag *)
Section StrongAltCon.
  Context (tc : TyCon)(dc:DataCon tc).

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
End StrongAltCon.

Definition mkStrongAltConPlusJunk' (tc : TyCon)(alt:AltCon) : ???(@StrongAltConPlusJunk tc).
  destruct alt.
  set (c:DataCon _) as dc.
  set ((dataConTyCon c):TyCon) as tc' in *.
  set (eqd_dec tc tc') as eqpf; destruct eqpf;
    [ idtac
      | apply (Error ("in a case of tycon "+++tyConToString tc+++", found a branch with datacon "+++dataConToString dc)) ]; subst.
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

Fixpoint mLetRecTypesVars {Γ} (mlr:Tree ??(WeakExprVar * WeakExpr)) φ : Tree ??(WeakExprVar * HaskType Γ) :=
  match mlr with
  | T_Leaf None         => []
  | T_Leaf (Some ((weakExprVar v t),e)) => [((weakExprVar v t),weakTypeToType φ t)]
  | T_Branch b1 b2 => ((mLetRecTypesVars b1 φ),,(mLetRecTypesVars b2 φ))
  end.

Open Scope string_scope.
Definition unlev {Γ:TypeEnv}(lht:LeveledHaskType Γ) : HaskType Γ   := match lht with t @@ l => t end.

Definition Indexed_Bind T f t (e:@Indexed T f t) : forall Q, (forall t, f t -> ???Q) -> ???Q.
intros.
destruct e; subst.
apply (Error error_message).
apply (X t f0).
Defined.
Notation "a >>>= b" := (@Indexed_Bind _ _ _ a _ b) (at level 20).

Definition DoublyIndexed_Bind T f t (e:@Indexed T (fun z => ???(f z)) t) : forall Q, (forall t, f t -> ???Q) -> ???Q.
  intros.
  eapply Indexed_Bind.
  apply e.
  intros.
  destruct X0.
  apply (Error error_message).
  apply (X t0 f0).
  Defined.

Notation "a >>>>= b" := (@DoublyIndexed_Bind _ _ _ a _ b) (at level 20).

Ltac matchTypes T1 T2 S :=
  destruct (eqd_dec T1 T2) as [matchTypes_pf|];
   [ idtac | apply (Error ("type mismatch in "+++S+++": " +++ (weakTypeToString T1) +++ " and " +++ (weakTypeToString T2))) ].
Ltac matchTypeVars T1 T2 S :=
  destruct (eqd_dec T1 T2) as [matchTypeVars_pf|];
   [ idtac | apply (Error ("type variable mismatch in"+++S)) ].
Ltac matchLevs L1 L2 S :=
  destruct (eqd_dec L1 L2) as [matchLevs_pf|];
   [ idtac | apply (Error ("level mismatch in "+++S)) ].


Definition cure {Γ}(ξ:WeakExprVar -> WeakType * list WeakTypeVar)(φ:WeakTypeVar->HaskTyVar Γ)
  : WeakExprVar->LeveledHaskType Γ :=
  fun wtv => weakTypeToType φ (fst (ξ wtv)) @@ map φ (snd (ξ wtv)).

Definition weakExprVarToWeakType : WeakExprVar -> WeakType :=
  fun wev => match wev with weakExprVar _ t => t end.
  Coercion weakExprVarToWeakType : WeakExprVar >-> WeakType.

Fixpoint upξ (ξ:WeakExprVar -> WeakType * list WeakTypeVar)
 (evs:list WeakExprVar)
 (lev:list WeakTypeVar) :
  (WeakExprVar -> WeakType * list WeakTypeVar) :=
  fun wev =>
  match evs with
    | nil  => ξ wev
    | a::b => if eqd_dec wev a then ((wev:WeakType),lev) else upξ ξ b lev wev
  end.

Variable weakCoercionToHaskCoercion : forall Γ Δ, WeakCoercion -> HaskCoercion Γ Δ.

Notation "'checkit' ( Y ) X" := (match weakTypeOfWeakExpr Y as CTE return
                                   CTE=weakTypeOfWeakExpr Y -> forall Γ Δ φ ψ ξ lev, Indexed _ CTE with
                                | Error s   =>   fun  _ _ _ _ _ _  _   => Indexed_Error _ s
                                | OK    cte =>  fun cte_pf => (fun x Γ Δ φ ψ ξ lev => Indexed_OK _ _ (x Γ Δ φ ψ ξ lev)) X
                              end (refl_equal _)) (at level 10).


(* equality lemmas I have yet to prove *)

Lemma upξ_lemma Γ ξ v lev φ
  : cure(Γ:=Γ) (upξ ξ (v :: nil) lev) φ = update_ξ (cure ξ φ) ((v,weakTypeToType φ v @@  map φ lev)::nil).
  admit.
  Qed.

(* this is tricky because of the test for ModalBoxTyCon is a type index for tc and because the fold is a left-fold *)

Lemma letrec_lemma : forall Γ ξ φ rb lev,
let ξ' := upξ ξ (map (@fst _ _) (leaves (mLetRecTypesVars rb φ))) lev in
(cure ξ' φ) = (
        update_ξ (cure ξ φ)
          (map
             (fun x : WeakExprVar * HaskType Γ =>
              ⟨fst x, snd x @@  map φ lev ⟩) (leaves (mLetRecTypesVars rb φ)))).
admit.
Qed.

Lemma case_lemma1 tc Γ avars' (sac:StrongAltConPlusJunk tc) vars ξ φ lev :
(@scbwv_ξ WeakExprVar WeakExprVarEqDecidable tc Γ avars'
        {| scbwv_sac := sac; scbwv_exprvars := vars |} 
        (@cure Γ ξ φ) (@map WeakTypeVar (HaskTyVar Γ) φ lev))
      = (cure ξ (sacpj_φ sac Γ φ)).
  admit.
  Qed.
Lemma case_lemma2 tc Γ  (sac:@StrongAltConPlusJunk tc)  φ lev :
  (map (sacpj_φ sac Γ φ) lev) = weakL' (map φ lev).
  admit.
  Qed.
Lemma case_lemma3 Γ φ t tc   (sac:@StrongAltConPlusJunk tc) :
 (weakT' (weakTypeToType φ t) = weakTypeToType (sacpj_φ sac Γ φ) t).
        admit.
  Qed.
Lemma case_lemma4 Γ φ (tc:TyCon) avars0 : forall Q1 Q2, (@weakTypeToType Γ φ Q2)=Q1 ->
   fold_left HaskAppT (map (weakTypeToType φ) avars0) Q1 =
   weakTypeToType φ (fold_left WAppTy avars0 Q2).
   induction avars0; intros.
   simpl.
   symmetry; auto.
   simpl.
   set (IHavars0 (HaskAppT Q1 (weakTypeToType φ a)) (WAppTy Q2 a)) as z.
   rewrite z.
   reflexivity.
   rewrite <- H.
   simpl.
   auto.
   Qed.

(* for now... *)
Axiom assume_all_coercions_well_formed : forall Γ (Δ:CoercionEnv Γ) t1 t2 co, Δ ⊢ᴄᴏ  co : t1 ∼ t2.
Axiom assume_all_types_well_formed     : forall Γ t x,    Γ ⊢ᴛy t : x.

Definition weakψ {Γ}{Δ:CoercionEnv Γ} {κ}(ψ:WeakCoerVar -> HaskCoVar Γ Δ) :
  WeakCoerVar -> HaskCoVar Γ (κ::Δ).
  intros.
  unfold HaskCoVar.
  intros.
  apply (ψ X TV CV env).
  inversion cenv; auto.
  Defined.

Lemma substRaw {Γ}{κ} : HaskType (κ::Γ) -> (∀ TV, @InstantiatedTypeEnv TV Γ -> TV -> @RawHaskType TV).
  intro ht.
  intro TV.
  intro env.
  intro tv.
  apply ht.
  apply (tv:::env).
  Defined.

Lemma substRaw_lemma : forall (Γ:TypeEnv) (φ:WeakTypeVar->HaskTyVar Γ) wt tsubst wtv,
  substT (substRaw (weakTypeToType (upφ wtv φ) wt)) (weakTypeToType φ tsubst) =
  weakTypeToType φ (replaceWeakTypeVar wt wtv tsubst).
  admit.
  Qed.

Definition weakExprToStrongExpr : forall
    (ce:WeakExpr)
    (Γ:TypeEnv)
    (Δ:CoercionEnv Γ)
    (φ:WeakTypeVar->HaskTyVar Γ)
    (ψ:WeakCoerVar->HaskCoVar Γ Δ)
    (ξ:WeakExprVar->WeakType * list WeakTypeVar)
    (lev:list WeakTypeVar)
    ,
    Indexed (fun t' => ???(@Expr _ WeakExprVarEqDecidable Γ Δ (cure ξ φ) (weakTypeToType φ t' @@ (map φ lev))))
       (weakTypeOfWeakExpr ce).
  refine ((
    fix weakExprToStrongExpr (ce:WeakExpr) {struct ce} : forall Γ Δ φ ψ ξ lev,
      Indexed (fun t' => ???(Expr Γ Δ (cure ξ φ) (weakTypeToType φ t' @@ (map φ lev)))) (weakTypeOfWeakExpr ce) :=
    (match ce as CE return (forall Γ Δ φ ψ ξ lev, Indexed _ (weakTypeOfWeakExpr CE))
      with
    | WEVar   v                   => let case_WEVar := tt in checkit (WEVar   v) (fun Γ Δ φ ψ ξ lev => _)
    | WELit   lit                 => let case_WELit := tt in checkit (WELit   lit) (fun Γ Δ φ ψ ξ lev => _)
    | WEApp   e1 e2               => let case_WEApp := tt in checkit (WEApp   e1 e2)       (fun Γ Δ φ ψ ξ lev =>
        weakExprToStrongExpr e1 Γ Δ φ ψ ξ lev >>>>= fun te1 e1' => 
          ((weakExprToStrongExpr e2 Γ Δ φ ψ ξ lev) >>>>= fun te2 e2' => _))
    | WETyApp e t                 => let case_WETyApp := tt in
      checkit (WETyApp e t) (fun Γ Δ φ ψ ξ lev => weakExprToStrongExpr e Γ Δ φ ψ ξ lev >>>>= fun te' e' => _)
    | WECoApp e t                 => let case_WECoApp := tt in
      checkit (WECoApp e t) (fun Γ Δ φ ψ ξ lev => weakExprToStrongExpr e Γ Δ φ ψ ξ lev >>>>= fun te' e' => _)
    | WELam   ev e                => let case_WELam   := tt in 
      checkit (WELam   ev e) (fun Γ Δ φ ψ ξ lev =>
        let ξ' := @upξ ξ (ev::nil) lev in
        weakExprToStrongExpr e Γ Δ φ ψ ξ' lev >>>>= fun te' e' => _)
    | WECoLam cv e                => let case_WECoLam := tt in
      checkit (WECoLam cv e) (fun Γ Δ φ ψ ξ lev => (fun e' => _) (weakExprToStrongExpr e))
    | WEBrak  ec e tbody              => let case_WEBrak  := tt in
      checkit (WEBrak  ec e tbody) (fun Γ Δ φ ψ ξ lev => weakExprToStrongExpr e Γ Δ φ ψ ξ (ec::lev) >>>>= fun te' e' => _)
    | WEEsc   ec e tbody              => 
      checkit (WEEsc   ec e tbody) (fun Γ Δ φ ψ ξ lev =>
        match lev as LEV return lev=LEV -> _ with
          | nil       => let case_WEEsc_bogus   := tt in _
          | ec'::lev' => fun ecpf =>  weakExprToStrongExpr e Γ Δ φ ψ ξ lev' >>>>= fun te' e' => let case_WEEsc   := tt in _
        end (refl_equal _))
    | WETyLam tv e                => let case_WETyLam := tt in
      checkit (WETyLam tv e) (fun Γ Δ φ ψ ξ lev => (fun e' => _) (weakExprToStrongExpr e))
    | WENote  n e                 => let case_WENote := tt in
      checkit (WENote  n e) (fun Γ Δ φ ψ ξ lev => weakExprToStrongExpr e Γ Δ φ ψ ξ lev >>>>= fun te' e' => _)
    | WECast  e co                => let case_WECast := tt in
      checkit (WECast  e co) (fun Γ Δ φ ψ ξ lev => weakExprToStrongExpr e Γ Δ φ ψ ξ lev >>>>= fun te' e' => _)
    | WELet   v ve  e             => let case_WELet   := tt in 
      checkit (WELet   v ve e) (fun Γ Δ φ ψ ξ lev =>
        let ξ' := upξ ξ (v::nil) lev in
          ((weakExprToStrongExpr e Γ Δ φ ψ ξ lev)
            >>>>= (fun te' e' => ((weakExprToStrongExpr ve Γ Δ φ ψ ξ' lev) >>>>= (fun vet' ve' => _)))))

    | WELetRec rb   e             => 
      checkit (WELetRec rb e) (fun Γ Δ φ ψ ξ lev =>
let ξ' := upξ ξ (map (@fst _ _) (leaves (mLetRecTypesVars rb φ))) lev in
          ((fix mLetRecBindingsToELetRecBindings (mlr:Tree ??(WeakExprVar * WeakExpr)) : forall Γ Δ φ ψ ξ lev,
            ???(ELetRecBindings Γ Δ (cure ξ φ) (map φ lev) (mLetRecTypesVars mlr φ)) :=
            match mlr as MLR return forall Γ Δ φ ψ ξ lev,
              ???(ELetRecBindings Γ Δ (cure ξ φ) (map φ lev) (mLetRecTypesVars MLR φ)) with
              | T_Leaf None       => fun Γ Δ φ ψ ξ lev => OK (ELR_nil _ _ _ _)
              | T_Leaf (Some  (cv,e)) => fun Γ Δ φ ψ ξ lev =>
                let case_mlr_leaf := tt in weakExprToStrongExpr e Γ Δ φ ψ ξ lev >>>>= fun me => _
              | T_Branch b1 b2   =>
                fun Γ Δ φ ψ ξ lev  => 
                  mLetRecBindingsToELetRecBindings b1 Γ Δ φ ψ ξ lev >>= fun x1' =>
                    mLetRecBindingsToELetRecBindings b2 Γ Δ φ ψ ξ lev >>= fun x2' =>
                      OK (ELR_branch _ _ _ _ _ _ x1' x2')
            end) rb Γ Δ φ ψ ξ' lev) >>= fun rb' => (weakExprToStrongExpr e Γ Δ φ ψ ξ' lev)
          >>>>= fun et' e' =>
      let case_MLLetRec := tt in _)
      
    | WECase  e tbranches tc avars alts =>
      checkit (WECase  e tbranches  tc avars alts) (fun Γ Δ φ ψ ξ lev =>
        list2vecOrFail avars _ (fun _ _ => "number of types provided did not match the tycon's number of universal tyvars in Case")
        >>= fun avars0 => 
          let avars' := vec_map (@weakTypeToType Γ φ) avars0 in
          let tbranches' := @weakTypeToType Γ φ tbranches in
            ((fix caseBranches (alts:Tree ??(AltCon*list WeakTypeVar*list WeakCoerVar*list WeakExprVar*WeakExpr))
              :
               ???(Tree ??{ scb : StrongCaseBranchWithVVs WeakExprVar _ tc avars'
                            & Expr (sac_Γ scb Γ)
                                   (sac_Δ scb Γ avars' (weakCK'' Δ))
                                   (scbwv_ξ scb (cure ξ φ) (map φ lev))
                                   (weakLT' (tbranches'@@(map φ lev))) }) :=
              match alts with
              | T_Leaf None             => OK []
              | T_Branch b1 b2          => caseBranches b1 >>= fun b1' => caseBranches b2 >>= fun b2' => OK (b1',,b2')
              | T_Leaf (Some (alt,tvars,cvars,vvars,e')) =>
                mkStrongAltConPlusJunk' tc alt >>= fun sac =>
                list2vecOrFail vvars (sac_numExprVars (sac:@StrongAltCon tc))
                (fun _ _ => "number of expression variables provided did not match the datacon's number of fields") >>= fun vars =>
                  let scb := @Build_StrongCaseBranchWithVVs WeakExprVar _ tc Γ avars' sac vars in
                  let rec 
                    := @weakExprToStrongExpr e'
                    (sac_Γ scb Γ)
                    (sac_Δ scb Γ avars' (weakCK'' Δ))
                    (sacpj_φ sac Γ φ)
                    (let case_psi := tt in _)
                    ξ
                    lev in (let case_ECase_leaf := tt in _)
              end
              ) alts) >>= fun alts' =>
            weakExprToStrongExpr e Γ Δ φ ψ ξ lev >>>>= fun te' e' =>
              let case_ECase := tt in _)
     end))); clear weakExprToStrongExpr.

    destruct case_WEVar; intros.
      matchTypes cte (fst (ξ v)) "HaskWeak EVar".
      rewrite matchTypes_pf.
      matchLevs (snd (ξ v)) lev "HaskWeak EVar".
      rewrite <- matchLevs_pf.
      apply OK.
      apply (EVar _ _ (cure ξ φ)).

    destruct case_WELit; intros.
      matchTypes (WTyCon (haskLiteralToTyCon lit)) cte "HaskWeak ELit".
      rewrite <- matchTypes_pf.
      apply OK.
      replace (weakTypeToType φ (WTyCon (haskLiteralToTyCon lit))) with (@literalType lit Γ); [ idtac | reflexivity].
      apply ELit.

    destruct case_WELet; intros.
      unfold ξ' in ve'.
      matchTypes te' v "HaskWeak ELet".
      rename matchTypes_pf into matchTypes_pf'.
      matchTypes cte vet' "HaskWeak ELet".
      apply OK.
      eapply ELet.
      apply e'.
      rewrite matchTypes_pf'.
      rewrite matchTypes_pf.
      rewrite upξ_lemma in ve'.
      apply ve'.

    destruct case_mlr_leaf; intros.
      simpl.
      destruct cv.
      matchTypes me w "HaskWeak LetRec".
      apply OK.
      apply ELR_leaf.
      rewrite <- matchTypes_pf.
      apply X.

    destruct case_MLLetRec; intros.
      matchTypes et' cte "HaskWeak LetRec".
      apply OK.
      unfold ξ' in rb'.
      rewrite (letrec_lemma Γ ξ φ rb lev) in rb'.
      apply (@ELetRec WeakExprVar _ Γ Δ (cure ξ φ) (map φ lev) (weakTypeToType φ cte) _ rb').
      rewrite <- (letrec_lemma Γ ξ φ rb lev).
      rewrite <- matchTypes_pf.
      apply e'.

    destruct case_WECast; intros.
      apply OK.
      apply (fun pf => @ECast WeakExprVar _ Γ Δ (cure ξ φ) (weakCoercionToHaskCoercion Γ Δ co) _ _ (map φ lev) pf e').
      apply assume_all_coercions_well_formed.

    destruct case_WENote; intros.
      matchTypes te' cte "HaskWeak ENote".
      apply OK.
      apply ENote.
      apply n.
      rewrite <- matchTypes_pf.
      apply e'.

    destruct case_WEApp; intros.
      matchTypes te1 (WAppTy (WAppTy WFunTyCon te2) cte) "HaskWeak EApp".
      inversion cte_pf.
      destruct (weakTypeOfWeakExpr e1); try apply (Error error_message).
      simpl in H0.
      destruct w; try apply (Error error_message); inversion H0.
      destruct w1; try apply (Error error_message); inversion H0.
      destruct w1_1; try apply (Error error_message); inversion H0.
      clear H0 H1 H2.
      rewrite matchTypes_pf in e1'.
      simpl in e1'.
      rewrite <- H3.
      apply (OK (EApp _ _ _ _ _ _ e1' e2')).

    destruct case_WETyApp; intros.
      inversion cte_pf.
      destruct (weakTypeOfWeakExpr e); simpl in *; inversion H0.
      clear H1.
      destruct w; inversion H0.
      simpl in cte_pf.
      clear cte_pf.
      rename w0 into wt.
      rename t into tsubst.
      rename w into wtv.
      set (@ETyApp WeakExprVar _ Γ Δ wtv
        (substRaw (weakTypeToType (upφ wtv φ) wt))
        (weakTypeToType φ tsubst)
        (cure ξ φ)
        (map φ lev)
        (assume_all_types_well_formed _ _ _)
      ) as q.

      (* really messy –– but it works! *)
      matchTypes te' (WForAllTy wtv wt) "HaskWeak ETyApp".
      apply OK.
      rewrite substRaw_lemma in q.
      apply q.
      clear q H1 H0.
      rewrite matchTypes_pf in e'.
      simpl in e'.
      unfold HaskTAll.
      unfold substRaw.
      apply e'.

    destruct case_WECoApp; intros.
      inversion cte_pf.
      destruct (weakTypeOfWeakExpr e); simpl in *; inversion H0.
      clear H1.
      destruct w; inversion H0.
      subst.
      destruct t as [ct1 ct2 cc].
      set (@ECoApp WeakExprVar _ Γ Δ (weakCoercionToHaskCoercion Γ Δ (weakCoercion ct1 ct2 cc))
              (weakTypeToType φ ct1) (weakTypeToType φ ct2) (weakTypeToType φ te') (cure ξ φ) (map φ lev)) as q.
      matchTypes w3 te' "HaskWeak ECoApp".
      rewrite matchTypes_pf.
      clear matchTypes_pf.
      matchTypes (WCoFunTy ct1 ct2 te') te' "HaskWeak ECoApp".
      apply OK.
      apply q.
      apply assume_all_coercions_well_formed.
      clear q H0 cte_pf.
      rewrite <- matchTypes_pf in e'.
      simpl in e'.
      apply e'.

    destruct case_WELam; intros.
      simpl in cte_pf.
      destruct ev as [evv evt].
      destruct (weakTypeOfWeakExpr e); simpl in cte_pf; inversion cte_pf; try apply (Error error_message).
      matchTypes te' w "HaskWeak ELam".
      rewrite <- matchTypes_pf.
      apply OK.
      simpl.
      eapply ELam.
      apply assume_all_types_well_formed.
      unfold ξ' in e'.
      rewrite upξ_lemma in e'.
      apply e'.

    destruct case_WETyLam; intros.
      inversion cte_pf.
      destruct tv.
      destruct (weakTypeOfWeakExpr e).
      inversion H0.
      inversion H0.
      set (e' (k::Γ) (weakCE Δ) (upφ (weakTypeVar c k) φ) (fun x => weakCV (ψ x)) ξ lev) as e''.
      inversion e''; try apply (Error error_message).
      inversion X; try apply (Error error_message).
      apply (Error "FIXME: HaskWeakToStrong: type lambda not yet implemented").

    destruct case_WECoLam; intros.
      inversion cte_pf.
      destruct cv.
      destruct (weakTypeOfWeakExpr e).
      inversion H0.
      inversion H0.
      set (e' Γ (weakTypeToType φ w ∼∼∼ weakTypeToType φ w0 :: Δ) φ (weakψ ψ) ξ lev) as q.
      inversion q.
      destruct X; try apply (Error error_message).
      set (kindOfType (weakTypeToType φ w)) as qq.
      destruct qq; try apply (Error error_message).
      apply OK.
      apply ECoLam with (κ:=k).
      apply assume_all_types_well_formed.
      apply assume_all_types_well_formed.
      fold (@weakTypeToType Γ).
      apply e0.

    destruct case_WEBrak; intros.
      simpl in cte_pf.
      destruct ec as [ecv eck].
      destruct (weakTypeOfWeakExpr e); inversion cte_pf; try apply (Error error_message).
      simpl.
      matchTypes te' w "HaskWeak EBrak".
      apply OK.
      apply EBrak.
      rewrite matchTypes_pf in e'.
      apply e'.

    destruct case_WEEsc_bogus; intros.
      apply (Error "attempt to use escape symbol at level zero").

    destruct case_WEEsc; intros.
      rewrite ecpf.
      clear ecpf lev.
      matchTypes te' (WCodeTy ec' cte) "HaskWeak EEsc".
      apply OK.
      apply EEsc.
      rewrite matchTypes_pf in e'.
      simpl in e'.
      apply e'.

    destruct case_psi.
      apply (sacpj_ψ sac Γ Δ avars' ψ).

    destruct case_ECase_leaf.
      inversion rec; try apply (Error error_message).
      destruct X; try apply (Error error_message).
      matchTypes tbranches t "HaskWeak ECase".
      apply OK.
      apply T_Leaf.
      apply Some.
      apply (existT _ {| scbwv_sac := scb ; scbwv_exprvars := vars |}).
      simpl.
      unfold tbranches'.
      rewrite matchTypes_pf.
      rewrite case_lemma1.
      rewrite <- case_lemma2.
      rewrite case_lemma3.
      apply e0.

    destruct case_ECase; intros.
      matchTypes cte tbranches "HaskWeak ECase". 
      rewrite matchTypes_pf.
      clear matchTypes_pf.
      matchTypes te' (fold_left WAppTy (vec2list avars0) (WTyCon tc)) "HaskWeak ECase".
      apply OK.
      apply (fun e => @ECase WeakExprVar _ Γ Δ (cure ξ φ) (map φ lev) tc _ _ e alts').
      unfold caseType.
      unfold avars'.
      replace (fold_left HaskAppT (vec2list (vec_map (weakTypeToType φ) avars0)) (HaskTCon tc))
        with (weakTypeToType φ (fold_left WAppTy (vec2list avars0) (WTyCon tc))).
      rewrite <- matchTypes_pf.
      apply e'.
      symmetry.
      rewrite <- vec2list_map_list2vec.
      apply case_lemma4.
      apply tc.
      reflexivity.
      Defined.
