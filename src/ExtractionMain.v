(*********************************************************************************************************************************)
(* ExtractionMain:                                                                                                               *)
(*                                                                                                                               *)
(*    This module is the "top level" for extraction                                                                              *)
(*                                                                                                                               *)
(*********************************************************************************************************************************)

Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Preamble.
Require Import General.

Require Import NaturalDeduction.
Require Import NaturalDeductionContext.

Require Import HaskKinds.
Require Import HaskLiterals.
Require Import HaskTyCons.
Require Import HaskCoreVars.
Require Import HaskCoreTypes.
Require Import HaskCore.
Require Import HaskWeakVars.
Require Import HaskWeakTypes.
Require Import HaskWeak.
Require Import HaskStrongTypes.
Require Import HaskStrong.
Require Import HaskProof.
Require Import HaskCoreToWeak.
Require Import HaskWeakToStrong.
Require Import HaskStrongToProof.
Require Import HaskProofToLatex.
Require Import HaskStrongToWeak.
Require Import HaskWeakToCore.
Require Import HaskProofToStrong.

Require Import HaskFlattener.

Open Scope string_scope.
Extraction Language Haskell.

(*Extract Inductive vec    => "([])" [ "([])" "(:)" ].*)
(*Extract Inductive Tree   => "([])" [ "([])" "(:)" ].*)
(*Extract Inlined Constant map => "Prelude.map".*)

(* I try to reuse Haskell types mostly to get the "deriving Show" aspect *)
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].
Extract Inductive list   => "([])" [ "([])" "(:)" ].
Extract Inductive string => "Prelude.String" [ "[]" "(:)" ].
Extract Inductive prod   => "(,)" [ "(,)" ].
Extract Inductive sum    => "Prelude.Either" [ "Prelude.Left" "Prelude.Right" ].
Extract Inductive sumbool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive bool    => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive unit    => "()" [ "()" ].
Extract Inlined Constant string_dec => "(==)".
Extract Inlined Constant ascii_dec => "(==)".

Extract Inductive ascii => "Char" [ "you_forgot_to_patch_coq" ] "you_forgot_to_patch_coq".
Extract Constant zero   => "'\000'".
Extract Constant one    => "'\001'".
Extract Constant shift  => "shiftAscii".

Unset Extraction Optimize.
Unset Extraction AutoInline.

Variable Name : Type.  Extract Inlined Constant Name => "Name.Name".
Variable mkSystemName : Unique -> string -> nat -> Name.
  Extract Inlined Constant mkSystemName =>
    "(\u s d -> Name.mkSystemName u (OccName.mkOccName (OccName.varNameDepth (nat2int d)) s))".
Variable mkTyVar : Name -> Kind -> CoreVar.
  Extract Inlined Constant mkTyVar => "(\n k -> Var.mkTyVar n (kindToCoreKind k))".
Variable mkCoVar : Name -> CoreType -> CoreType -> CoreVar.
  Extract Inlined Constant mkCoVar => "(\n t1 t2 -> Var.mkCoVar n (Coercion.mkCoType t1 t2))".
Variable mkExVar : Name -> CoreType -> CoreVar.
  Extract Inlined Constant mkExVar => "Id.mkLocalId".

Section core2proof.
  Context (ce:@CoreExpr CoreVar).

  Definition Γ : TypeEnv := nil.

  Definition Δ : CoercionEnv Γ := nil.

  Definition φ : TyVarResolver Γ :=
    fun cv => Error ("unbound tyvar: " +++ toString (cv:CoreVar)).
    (*fun tv => error ("tried to get the representative of an unbound tyvar:" +++ (getCoreVarOccString tv)).*)

  Definition ψ : CoVarResolver Γ Δ :=
    fun cv => Error ("tried to get the representative of an unbound covar!" (*+++ (getTypeVarOccString cv)*)).

  (* We need to be able to resolve unbound exprvars, but we can be sure their types will have no
   * free tyvars in them *)
  Definition ξ (cv:CoreVar) : LeveledHaskType Γ ★ :=
    match coreVarToWeakVar' cv with
      | OK (WExprVar wev) => match weakTypeToTypeOfKind φ wev ★ with
                          | Error s => Prelude_error ("Error converting weakType of top-level variable "+++
                                                         toString cv+++": " +++ s)
                          | OK    t => t @@ nil
                        end
      | OK (WTypeVar _)   => Prelude_error "top-level xi got a type variable"
      | OK (WCoerVar _)   => Prelude_error "top-level xi got a coercion variable"
      | Error s           => Prelude_error s
    end.

  Definition header : string :=
    "\documentclass{article}"+++eol+++
    "\usepackage{amsmath}"+++eol+++
    "\usepackage{amssymb}"+++eol+++
    "\usepackage{proof}"+++eol+++
    "\usepackage{trfrac}       % http://www.utdallas.edu/~hamlen/trfrac.sty"+++eol+++
    "\def\code#1#2{\Box_{#1} #2}"+++eol+++
    "\usepackage[paperwidth=\maxdimen,paperheight=\maxdimen]{geometry}"+++eol+++
    "\usepackage[tightpage,active]{preview}"+++eol+++
    "\begin{document}"+++eol+++
    "\setlength\PreviewBorder{5pt}"+++eol.

  Definition footer : string :=
    eol+++"\end{document}"+++
    eol.

  (* core-to-string (-dcoqpass) *)
  Definition coreToStringExpr' (ce:@CoreExpr CoreVar) : ???string :=
    addErrorMessage ("input CoreSyn: " +++ toString ce)
    (addErrorMessage ("input CoreType: " +++ toString (coreTypeOfCoreExpr ce)) (
      coreExprToWeakExpr ce >>= fun we =>
        addErrorMessage ("WeakExpr: " +++ toString we)
          ((addErrorMessage ("CoreType of WeakExpr: " +++ toString (coreTypeOfCoreExpr (weakExprToCoreExpr we)))
            ((weakTypeOfWeakExpr we) >>= fun t =>
              (addErrorMessage ("WeakType: " +++ toString t)
                ((weakTypeToTypeOfKind φ t ★) >>= fun τ =>
                  addErrorMessage ("HaskType: " +++ toString τ)
                  ((weakExprToStrongExpr Γ Δ φ ψ ξ (fun _ => false) τ nil we) >>= fun e =>
                    OK (eol+++eol+++eol+++
                        "\begin{preview}"+++eol+++
                        "$\displaystyle "+++
                        toString (nd_ml_toLatexMath (@expr2proof _ _ _ _ _ _ _ e))+++
                        " $"+++eol+++
                        "\end{preview}"+++eol+++eol+++eol)
                  )))))))).

  Definition coreToStringExpr (ce:@CoreExpr CoreVar) : string :=
    match coreToStringExpr' ce with
      | OK x => x
      | Error s => Prelude_error s
    end.

  Definition coreToStringBind (binds:@CoreBind CoreVar) : string :=
    match binds with
      | CoreNonRec _ e => coreToStringExpr e
      | CoreRec    lbe => fold_left (fun x y => x+++eol+++eol+++y) (map (fun x => coreToStringExpr (snd x)) lbe) ""
    end.

  Definition coqPassCoreToString (lbinds:list (@CoreBind CoreVar)) : string :=
    header +++
    (fold_left (fun x y => x+++eol+++eol+++y) (map coreToStringBind lbinds) "")
    +++ footer.


  (* core-to-core (-fcoqpass) *)
  Section CoreToCore.

    Definition mkWeakTypeVar (u:Unique)(k:Kind)                 : WeakTypeVar :=
      weakTypeVar (mkTyVar (mkSystemName u "tv" O) k) k.
    Definition mkWeakCoerVar (u:Unique)(k:Kind)(t1 t2:WeakType) : WeakCoerVar :=
      weakCoerVar (mkCoVar (mkSystemName u "cv" O) (weakTypeToCoreType t1) (weakTypeToCoreType t2)) t1 t2.
    Definition mkWeakExprVar (u:Unique)(t:WeakType)             : WeakExprVar :=
      weakExprVar (mkExVar (mkSystemName u "ev" O) (weakTypeToCoreType t)) t.

    Context (hetmet_brak    : WeakExprVar).
    Context (hetmet_esc     : WeakExprVar).
    Context (hetmet_flatten : WeakExprVar).
    Context (hetmet_unflatten : WeakExprVar).
    Context (hetmet_flattened_id : WeakExprVar).
    Context (uniqueSupply   : UniqSupply).

    Definition useUniqueSupply {T}(ut:UniqM T) : ???T :=
      match ut with
        uniqM f =>
         f uniqueSupply >>= fun x => OK (snd x)
      end.

    Definition larger : forall ln:list nat, { n:nat & forall n', In n' ln -> gt n n' }.
      intros.
      induction ln.
      exists O.
      intros.
      inversion H.
      destruct IHln as [n pf].
      exists (plus (S n) a).
      intros.
      destruct H.
      omega.
      fold (@In _ n' ln) in H.
      set (pf n' H) as q.
      omega.
      Defined.
 
  Definition FreshNat : @FreshMonad nat.
    refine {| FMT       := fun T => nat -> prod nat T
            ; FMT_fresh := _
           |}.
    Focus 2.
    intros.
    refine ((S H),_).
    set (larger tl) as q.
    destruct q as [n' pf].
    exists n'.
    intros.
    set (pf _ H0) as qq.
    omega.
    
    refine {| returnM := fun a (v:a) => _ |}.
      intro n. exact (n,v).
      intros.
      set (X H) as q.
      destruct q as [n' v].
      set (X0 v n') as q'.
      exact q'.
      Defined.

    Definition unFresh {T} : @FreshM _ FreshNat T -> T.
      intros.
      destruct X.
      exact O.
      apply t.
      Defined.

  End CoreToCore.

  Definition coreVarToWeakExprVarOrError cv :=
    match addErrorMessage ("in coreVarToWeakExprVarOrError" +++ eol) (coreVarToWeakVar' cv) with
      | OK (WExprVar wv) => wv
      | Error s     => Prelude_error s
      | _           => Prelude_error "IMPOSSIBLE"
    end.

  Definition curry {Γ}{Δ}{a}{s}{Σ}{lev} :
    ND Rule 
       [ Γ > Δ > Σ             |- [a ---> s  ]@lev ]
       [ Γ > Δ > [a @@ lev],,Σ |-       [ s ]@lev ].
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply AExch ].
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RApp ].
    eapply nd_comp; [ apply nd_rlecnac | idtac ].
    apply nd_prod.
    apply nd_id.
    apply nd_rule.
    apply RVar.
    Defined.

  Definition fToC1 {Γ}{Δ}{a}{s}{lev} :
    ND Rule [] [ Γ > Δ > [        ] |- [a ---> s  ]@lev ] ->
    ND Rule [] [ Γ > Δ > [a @@ lev] |-       [ s  ]@lev ].
    intro pf.
    eapply nd_comp.
    apply pf.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; apply ACanR ].
    apply curry.
    Defined.

  Definition fToC2 {Γ}{Δ}{a1}{a2}{s}{lev} :
    ND Rule [] [ Γ > Δ >                       [] |- [a1 ---> (a2 ---> s)  ]@lev ] ->
    ND Rule [] [ Γ > Δ > [a1 @@ lev],,[a2 @@ lev] |-                  [ s  ]@lev ].
    intro pf.
    eapply nd_comp.
    eapply pf.
    clear pf.
    eapply nd_comp.
    eapply curry.
    eapply nd_comp.
    eapply nd_rule.
    eapply RArrange.
    eapply ACanR.
    eapply nd_comp; [ idtac | eapply nd_rule; eapply RArrange; eapply AExch ].
    apply curry.
    Defined.

  Section coqPassCoreToCore.
    Context
    (do_flatten : bool)
    (do_skolemize : bool)
    (hetmet_brak  : CoreVar)
    (hetmet_esc   : CoreVar)
    (hetmet_flatten : CoreVar)
    (hetmet_unflatten : CoreVar)
    (hetmet_flattened_id : CoreVar)
    (uniqueSupply : UniqSupply)
    (lbinds:list (@CoreBind CoreVar))
    (hetmet_PGArrowTyCon : TyFun)
    (hetmet_PGArrow_unit_TyCon : TyFun)
    (hetmet_PGArrow_tensor_TyCon : TyFun)
    (hetmet_PGArrow_exponent_TyCon : TyFun)
    (hetmet_pga_id : CoreVar)
    (hetmet_pga_comp : CoreVar)
    (hetmet_pga_first : CoreVar)
    (hetmet_pga_second : CoreVar)
    (hetmet_pga_cancell : CoreVar)
    (hetmet_pga_cancelr : CoreVar)
    (hetmet_pga_uncancell : CoreVar)
    (hetmet_pga_uncancelr : CoreVar)
    (hetmet_pga_assoc : CoreVar)
    (hetmet_pga_unassoc : CoreVar)
    (hetmet_pga_copy : CoreVar)
    (hetmet_pga_drop : CoreVar)
    (hetmet_pga_swap : CoreVar)
    (hetmet_pga_applyl : CoreVar)
    (hetmet_pga_applyr : CoreVar)
    (hetmet_pga_curryl : CoreVar)
    (hetmet_pga_curryr : CoreVar)
    .


    Definition ga_unit TV (ec:RawHaskType TV ECKind) : RawHaskType TV ★ :=
      @TyFunApp TV hetmet_PGArrow_unit_TyCon (ECKind::nil) ★ (TyFunApp_cons _ _ ec TyFunApp_nil).

    Definition ga_prod TV (ec:RawHaskType TV ECKind) (a b:RawHaskType TV ★) : RawHaskType TV ★  :=
      (@TyFunApp TV
        hetmet_PGArrow_tensor_TyCon
        (ECKind::★ ::★ ::nil) ★
        (TyFunApp_cons _ _ ec
          (TyFunApp_cons _ _ a
            (TyFunApp_cons _ _ b
          TyFunApp_nil)))).

    Definition ga_type {TV}(a:RawHaskType TV ECKind)(b c:RawHaskType TV ★) : RawHaskType TV ★ :=
      TApp (TApp (TApp (@TyFunApp TV 
        hetmet_PGArrowTyCon
        nil _ TyFunApp_nil) a) b) c.

    Definition ga := @ga_mk ga_unit ga_prod (@ga_type).

    Definition ga_type' {Γ}(a:HaskType Γ ECKind)(b c:HaskType Γ ★) : HaskType Γ ★ :=
      fun TV ite => TApp (TApp (TApp (@TyFunApp TV 
        hetmet_PGArrowTyCon
        nil _ TyFunApp_nil) (a TV ite)) (b TV ite)) (c TV ite).

    Definition mkGlob2' {Γ}{κ₁}{κ₂}(f:HaskType Γ κ₁ -> HaskType Γ κ₂ -> HaskType Γ ★) :
      IList Kind (fun κ : Kind => HaskType Γ κ) (κ₁::κ₂::nil) -> HaskType Γ ★.
      intros.
      inversion X; subst.
      inversion X1; subst.
      apply f; auto.
      Defined.

    Definition mkGlob2 {Γ}{Δ}{l}{κ₁}{κ₂}(cv:CoreVar)(f:HaskType Γ κ₁ -> HaskType Γ κ₂ -> HaskType Γ ★) x y
      : ND Rule [] [ Γ > Δ > [] |- [f x y ]@l ].
      apply nd_rule.
      refine (@RGlobal Γ Δ l 
        {| glob_wv    := coreVarToWeakExprVarOrError cv
          ; glob_kinds := κ₁ :: κ₂ :: nil
          ; glob_tf    := mkGlob2'(Γ:=Γ) f
          |} (ICons _ _ x (ICons _ _ y INil))).
      Defined.

    Definition mkGlob3' {Γ}{κ₁}{κ₂}{κ₃}(f:HaskType Γ κ₁ -> HaskType Γ κ₂ -> HaskType Γ κ₃ -> HaskType Γ ★) :
      IList Kind (fun κ : Kind => HaskType Γ κ) (κ₁::κ₂::κ₃::nil) -> HaskType Γ ★.
      intros.
      inversion X; subst.
      inversion X1; subst.
      inversion X3; subst.
      apply f; auto.
      Defined.

    Definition mkGlob3 {Γ}{Δ}{l}{κ₁}{κ₂}{κ₃}(cv:CoreVar)(f:HaskType Γ κ₁ -> HaskType Γ κ₂ -> HaskType Γ κ₃ -> HaskType Γ ★) x y z
      : ND Rule [] [ Γ > Δ > [] |- [f x y z ]@l ].
      apply nd_rule.
      refine (@RGlobal Γ Δ l 
        {| glob_wv    := coreVarToWeakExprVarOrError cv
          ; glob_kinds := κ₁ :: κ₂ :: κ₃ :: nil
          ; glob_tf    := mkGlob3'(Γ:=Γ) f
          |} (ICons _ _ x (ICons _ _ y (ICons _ _ z INil)))).
      Defined.

    Definition mkGlob4' {Γ}{κ₁}{κ₂}{κ₃}{κ₄}(f:HaskType Γ κ₁ -> HaskType Γ κ₂ -> HaskType Γ κ₃ -> HaskType Γ κ₄ -> HaskType Γ ★) :
      IList Kind (fun κ : Kind => HaskType Γ κ) (κ₁::κ₂::κ₃::κ₄::nil) -> HaskType Γ ★.
      intros.
      inversion X; subst.
      inversion X1; subst.
      inversion X3; subst.
      inversion X5; subst.
      apply f; auto.
      Defined.

    Definition mkGlob4 {Γ}{Δ}{l}{κ₁}{κ₂}{κ₃}{κ₄}(cv:CoreVar)(f:HaskType Γ κ₁ -> HaskType Γ κ₂ -> HaskType Γ κ₃ -> HaskType Γ κ₄ -> HaskType Γ ★) x y z q
      : ND Rule [] [ Γ > Δ > [] |- [f x y z q ] @l].
      apply nd_rule.
      refine (@RGlobal Γ Δ l 
        {| glob_wv    := coreVarToWeakExprVarOrError cv
          ; glob_kinds := κ₁ :: κ₂ :: κ₃ :: κ₄ :: nil
          ; glob_tf    := mkGlob4'(Γ:=Γ) f
          |} (ICons _ _ x (ICons _ _ y (ICons _ _ z (ICons _ _ q INil))))).
      Defined.

    Definition gat {Γ} ec (x:Tree ??(HaskType Γ ★))  := @ga_mk_tree ga_unit ga_prod _ ec x.

    Instance my_ga : garrow ga_unit ga_prod (@ga_type) :=
    { ga_id        := fun Γ Δ ec l a     => mkGlob2 hetmet_pga_id        (fun ec a => ga_type' ec a a) ec (gat ec a)
    ; ga_cancelr   := fun Γ Δ ec l a     => mkGlob2 hetmet_pga_cancelr   (fun ec a => ga_type' ec _ a) ec (gat ec a)
    ; ga_cancell   := fun Γ Δ ec l a     => mkGlob2 hetmet_pga_cancell   (fun ec a => ga_type' ec _ a) ec (gat ec a)
    ; ga_uncancelr := fun Γ Δ ec l a     => mkGlob2 hetmet_pga_uncancelr (fun ec a => ga_type' ec a _) ec (gat ec a)
    ; ga_uncancell := fun Γ Δ ec l a     => mkGlob2 hetmet_pga_uncancell (fun ec a => ga_type' ec a _) ec (gat ec a)
    ; ga_assoc     := fun Γ Δ ec l a b c => mkGlob4 hetmet_pga_assoc     (fun ec a b c => ga_type' ec _ _) ec (gat ec a) (gat ec b) (gat ec c)
    ; ga_unassoc   := fun Γ Δ ec l a b c => mkGlob4 hetmet_pga_unassoc   (fun ec a b c => ga_type' ec _ _) ec (gat ec a) (gat ec b) (gat ec c)
    ; ga_swap      := fun Γ Δ ec l a b   => mkGlob3 hetmet_pga_swap      (fun ec a b => ga_type' ec _ _) ec (gat ec a) (gat ec b)
    ; ga_drop      := fun Γ Δ ec l a     => mkGlob2 hetmet_pga_drop      (fun ec a => ga_type' ec _ _) ec (gat ec a)
    ; ga_copy      := fun Γ Δ ec l a     => mkGlob2 hetmet_pga_copy      (fun ec a => ga_type' ec _ _) ec (gat ec a)
    ; ga_first     := fun Γ Δ ec l a b x => fToC1 (mkGlob4 hetmet_pga_first (fun ec a b c => _) ec (gat ec a) (gat ec b) (gat ec x))
    ; ga_second    := fun Γ Δ ec l a b x => fToC1 (mkGlob4 hetmet_pga_second (fun ec a b c => _) ec (gat ec a) (gat ec b) (gat ec x))
    ; ga_comp      := fun Γ Δ ec l a b c => fToC2 (mkGlob4 hetmet_pga_comp (fun ec a b c => _) ec (gat ec a) (gat ec b) (gat ec c))
(*  ; ga_lit       := fun Γ Δ ec l a => nd_rule (RGlobal _ _ _ _ (coreVarToWeakExprVarOrError hetmet_pga_lit))*)
(*  ; ga_curry     := fun Γ Δ ec l a => nd_rule (RGlobal _ _ _ _ (coreVarToWeakExprVarOrError hetmet_pga_curry))*)
(*  ; ga_apply     := fun Γ Δ ec l a => nd_rule (RGlobal _ _ _ _ (coreVarToWeakExprVarOrError hetmet_pga_apply))*)
(*  ; ga_kappa     := fun Γ Δ ec l a     => fToC1 (nd_rule (RGlobal _ _ _ _ (coreVarToWeakExprVarOrError hetmet_pga_kappa)))*)
    ; ga_lit       := fun Γ Δ ec l a     => Prelude_error "ga_lit"
    ; ga_curry     := fun Γ Δ ec l a b c => Prelude_error "ga_curry"
    ; ga_apply     := fun Γ Δ ec l a b c => Prelude_error "ga_apply"
    ; ga_kappa     := fun Γ Δ ec l a     => Prelude_error "ga_kappa"
    }.

    Definition hetmet_brak' := coreVarToWeakExprVarOrError hetmet_brak.
    Definition hetmet_esc'  := coreVarToWeakExprVarOrError hetmet_esc.
    Definition hetmet_flatten'  := coreVarToWeakExprVarOrError hetmet_flatten.
    Definition hetmet_unflatten'  := coreVarToWeakExprVarOrError hetmet_unflatten.
    Definition hetmet_flattened_id'  := coreVarToWeakExprVarOrError hetmet_flattened_id.

    Definition coreToCoreExpr' (cex:@CoreExpr CoreVar) : ???(@CoreExpr CoreVar) :=
      addErrorMessage ("input CoreSyn: " +++ toString cex)
      (addErrorMessage ("input CoreType: " +++ toString (coreTypeOfCoreExpr cex)) (
        coreExprToWeakExpr cex >>= fun we =>
          addErrorMessage ("WeakExpr: " +++ toString we)
            ((addErrorMessage ("CoreType of WeakExpr: " +++ toString (coreTypeOfCoreExpr (weakExprToCoreExpr we)))
              ((weakTypeOfWeakExpr we) >>= fun t =>
                (addErrorMessage ("WeakType: " +++ toString t)
                  ((weakTypeToTypeOfKind φ t ★) >>= fun τ =>

                    ((weakExprToStrongExpr Γ Δ φ ψ ξ (fun _ => true) τ nil we) >>= fun e =>

                      (addErrorMessage ("HaskStrong...")
                        (if do_skolemize
                        then
                             (let haskProof := skolemize_and_flatten_proof hetmet_flatten' hetmet_unflatten'
                                                 hetmet_flattened_id' my_ga (@expr2proof _ _ _ _ _ _ _ e)
                              in (* insert HaskProof-to-HaskProof manipulations here *)
                              OK ((@proof2expr nat _ FreshNat _ _ (flatten_type τ) nil _
                                (fun _ => Prelude_error "unbound unique") _ haskProof) O)
                              >>= fun e' => (snd e') >>= fun e'' =>
                              strongExprToWeakExpr hetmet_brak' hetmet_esc'
                                mkWeakTypeVar mkWeakCoerVar mkWeakExprVar uniqueSupply
                                (projT2 e'') INil
                              >>= fun q => OK (weakExprToCoreExpr q))
                        else (if do_flatten
                        then
                          (let haskProof := flatten_proof (*hetmet_flatten' hetmet_unflatten'
                                                 hetmet_flattened_id' my_ga*) (@expr2proof _ _ _ _ _ _ _ e)
                              in (* insert HaskProof-to-HaskProof manipulations here *)
                              OK ((@proof2expr nat _ FreshNat _ _ τ nil _
                                (fun _ => Prelude_error "unbound unique") _ haskProof) O)
                              >>= fun e' => (snd e') >>= fun e'' =>
                              strongExprToWeakExpr hetmet_brak' hetmet_esc'
                                mkWeakTypeVar mkWeakCoerVar mkWeakExprVar uniqueSupply
                                (projT2 e'') INil
                              >>= fun q => OK (weakExprToCoreExpr q))
                        else
                          (let haskProof := @expr2proof _ _ _ _ _ _ _ e
                              in (* insert HaskProof-to-HaskProof manipulations here *)
                              OK ((@proof2expr nat _ FreshNat _ _ τ nil _
                                (fun _ => Prelude_error "unbound unique") _ haskProof) O)
                              >>= fun e' => (snd e') >>= fun e'' =>
                              strongExprToWeakExpr hetmet_brak' hetmet_esc'
                                mkWeakTypeVar mkWeakCoerVar mkWeakExprVar uniqueSupply
                                (projT2 e'') INil
                              >>= fun q => OK (weakExprToCoreExpr q))))
                  ))))))))).

    Definition coreToCoreExpr (ce:@CoreExpr CoreVar) : (@CoreExpr CoreVar) :=
      match coreToCoreExpr' ce with
        | OK x    => x
        | Error s => Prelude_error s
      end.

    Definition coreToCoreBind (binds:@CoreBind CoreVar) : @CoreBind CoreVar :=
      match binds with
        | CoreNonRec v e => let e' := coreToCoreExpr e in CoreNonRec (setVarType v (coreTypeOfCoreExpr e')) e'

        | CoreRec    lbe => CoreRec (map (fun ve => match ve with (v,e) => (v,coreToCoreExpr e) end) lbe)
                            (* FIXME: doesn't deal with the case where top level recursive binds change type *)
(*
          match coreToCoreExpr (CoreELet lbe) (CoreELit HaskMachNullAddr) with
            | CoreELet (CoreRec lbe') => lbe'
            | x                       => Prelude_error
                                            ("coreToCoreExpr was given a letrec, " +++
                                             "but returned something that wasn't a letrec: " +++ toString x)
          end
*)
      end.

    Definition coqPassCoreToCore' (lbinds:list (@CoreBind CoreVar)) : list (@CoreBind CoreVar) :=
      map coreToCoreBind lbinds.

  End coqPassCoreToCore.

    Definition coqPassCoreToCore 
    (do_flatten  : bool)
    (do_skolemize  : bool)
    (hetmet_brak  : CoreVar)
    (hetmet_esc   : CoreVar)
    (hetmet_flatten   : CoreVar)
    (hetmet_unflatten   : CoreVar)
    (hetmet_flattened_id   : CoreVar)
    (uniqueSupply : UniqSupply)
    (lbinds:list (@CoreBind CoreVar))
    (hetmet_PGArrowTyCon : TyFun)
    (hetmet_PGArrow_unit_TyCon : TyFun)
    (hetmet_PGArrow_tensor_TyCon : TyFun)
    (hetmet_PGArrow_exponent_TyCon : TyFun)
    (hetmet_pga_id : CoreVar)
    (hetmet_pga_comp : CoreVar)
    (hetmet_pga_first : CoreVar)
    (hetmet_pga_second : CoreVar)
    (hetmet_pga_cancell : CoreVar)
    (hetmet_pga_cancelr : CoreVar)
    (hetmet_pga_uncancell : CoreVar)
    (hetmet_pga_uncancelr : CoreVar)
    (hetmet_pga_assoc : CoreVar)
    (hetmet_pga_unassoc : CoreVar)
    (hetmet_pga_copy : CoreVar)
    (hetmet_pga_drop : CoreVar)
    (hetmet_pga_swap : CoreVar)
    (hetmet_pga_applyl : CoreVar)
    (hetmet_pga_applyr : CoreVar)
    (hetmet_pga_curryl : CoreVar)
    (hetmet_pga_curryr : CoreVar) : list (@CoreBind CoreVar) :=
    coqPassCoreToCore'
       do_flatten
       do_skolemize
       hetmet_brak  
       hetmet_esc   
       hetmet_flatten
       hetmet_unflatten
       hetmet_flattened_id
       uniqueSupply 
       hetmet_PGArrowTyCon
       hetmet_PGArrow_unit_TyCon
       hetmet_PGArrow_tensor_TyCon
(*       hetmet_PGArrow_exponent_TyCon*)
       hetmet_pga_id 
       hetmet_pga_comp 
       hetmet_pga_first 
       hetmet_pga_second 
       hetmet_pga_cancell 
       hetmet_pga_cancelr 
       hetmet_pga_uncancell 
       hetmet_pga_uncancelr 
       hetmet_pga_assoc 
       hetmet_pga_unassoc 
       hetmet_pga_copy 
       hetmet_pga_drop 
       hetmet_pga_swap 
       lbinds
       (*
       hetmet_pga_applyl 
       hetmet_pga_applyr 
       hetmet_pga_curryl 
       *)

       .

End core2proof.
