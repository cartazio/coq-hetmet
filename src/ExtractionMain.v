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
Require Import NaturalDeductionToLatex.

Require Import HaskKinds.
Require Import HaskLiteralsAndTyCons.
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

Require Import HaskProofCategory.
(*
Require Import HaskStrongCategory.
Require Import ReificationsEquivalentToGeneralizedArrows.
Require Import ProgrammingLanguage.
*)

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

(* adapted from ExtrOcamlString.v *)
Extract Inductive ascii => "Char" [ "bin2ascii" ] "bin2ascii'".
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
  Extract Inlined Constant mkCoVar => "(\n t1 t2 -> Var.mkCoVar n (Coercion.mkCoKind t1 t2))".
Variable mkExVar : Name -> CoreType -> CoreVar.
  Extract Inlined Constant mkExVar => "Id.mkLocalId".

Section core2proof.
  Context (ce:@CoreExpr CoreVar).

  Definition Γ : TypeEnv := nil.

  Definition Δ : CoercionEnv Γ := nil.

  Definition φ : TyVarResolver Γ :=
    fun cv => Error ("unbound tyvar: " +++ (cv:CoreVar)).
    (*fun tv => error ("tried to get the representative of an unbound tyvar:" +++ (getCoreVarOccString tv)).*)

  Definition ψ : CoVarResolver Γ Δ :=
    fun cv => Error ("tried to get the representative of an unbound covar!" (*+++ (getTypeVarOccString cv)*)).

  (* We need to be able to resolve unbound exprvars, but we can be sure their types will have no
   * free tyvars in them *)
  Definition ξ (cv:CoreVar) : LeveledHaskType Γ ★ :=
    match coreVarToWeakVar cv with
      | WExprVar wev => match weakTypeToTypeOfKind φ wev ★ with
                          | Error s => Prelude_error ("Error in top-level xi: " +++ s)
                          | OK    t => t @@ nil
                        end
      | WTypeVar _   => Prelude_error "top-level xi got a type variable"
      | WCoerVar _   => Prelude_error "top-level xi got a coercion variable"
    end.


  (* core-to-string (-dcoqpass) *)

  Definition header : string :=
    "\documentclass[9pt]{article}"+++eol+++
    "\usepackage{amsmath}"+++eol+++
    "\usepackage{amssymb}"+++eol+++
    "\usepackage{proof}"+++eol+++
    "\usepackage{mathpartir}   % http://cristal.inria.fr/~remy/latex/"+++eol+++
    "\usepackage{trfrac}       % http://www.utdallas.edu/~hamlen/trfrac.sty"+++eol+++
    "\def\code#1#2{\Box_{#1} #2}"+++eol+++
    "\usepackage[paperwidth=200in,centering]{geometry}"+++eol+++
    "\usepackage[displaymath,tightpage,active]{preview}"+++eol+++
    "\begin{document}"+++eol+++
    "\begin{preview}"+++eol.

  Definition footer : string :=
    eol+++"\end{preview}"+++
    eol+++"\end{document}"+++
    eol.


  Definition coreToStringExpr' (ce:@CoreExpr CoreVar) : ???string := Error "Temporarily Disabled".
(*
    addErrorMessage ("input CoreSyn: " +++ ce)
    (addErrorMessage ("input CoreType: " +++ coreTypeOfCoreExpr ce) (
      coreExprToWeakExpr ce >>= fun we =>
        addErrorMessage ("WeakExpr: " +++ we)
          ((addErrorMessage ("CoreType of WeakExpr: " +++ coreTypeOfCoreExpr (weakExprToCoreExpr we))
            ((weakTypeOfWeakExpr we) >>= fun t =>
              (addErrorMessage ("WeakType: " +++ t)
                ((weakTypeToTypeOfKind φ t ★) >>= fun τ =>
                  addErrorMessage ("HaskType: " +++ τ)
                  ((weakExprToStrongExpr Γ Δ φ ψ ξ (fun _ => false) τ nil we) >>= fun e =>
                    OK (eol+++"$$"+++ nd_ml_toLatex (@expr2proof _ _ _ _ _ _ e)+++"$$"+++eol)
                  )))))))).*)

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
      weakCoerVar (mkCoVar (mkSystemName u "cv" O) (weakTypeToCoreType t1) (weakTypeToCoreType t2)) k t1 t2.
    Definition mkWeakExprVar (u:Unique)(t:WeakType)             : WeakExprVar :=
      weakExprVar (mkExVar (mkSystemName u "ev" O) (weakTypeToCoreType t)) t.

    Context (hetmet_brak  : WeakExprVar).
    Context (hetmet_esc   : WeakExprVar).
    Context (uniqueSupply : UniqSupply).

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

    Definition env := ★::nil.
    Definition freshTV : HaskType env ★ := haskTyVarToType (FreshHaskTyVar _).
    Definition idproof0 : ND Rule [] [env > nil > [] |- [freshTV--->freshTV @@ nil]].
      eapply nd_comp.
      eapply nd_comp.
      eapply nd_rule.
      apply RVar.
      eapply nd_rule.
      eapply (RURule _ _ _ _ (RuCanL _ _)) .
      eapply nd_rule.
      eapply RLam.
      Defined.
(*
    Definition TInt : HaskType nil ★.
      assert (tyConKind' intPrimTyCon = ★).
        rewrite <- H.
        unfold HaskType; intros.
        apply TCon.
        Defined.

    Definition idproof1 : ND Rule [] [nil > nil > [TInt @@ nil] |- [TInt @@ nil]].
      apply nd_rule.
      apply RVar.
      Defined.

    Definition idtype :=
        HaskTAll(Γ:=nil) ★ (fun TV ite tv => (TApp (TApp TArrow (TVar tv)) (TVar tv))).

    Definition idproof : ND Rule [] [nil > nil > [] |- [idtype @@ nil]].
      eapply nd_comp; [ idtac | eapply nd_rule ; eapply RAbsT ].
      apply idproof0.
      Defined.
*)
(*
    Definition coreToCoreExpr' (ce:@CoreExpr CoreVar) : ???(@CoreExpr CoreVar) :=
    addErrorMessage ("input CoreSyn: " +++ ce)
    (addErrorMessage ("input CoreType: " +++ coreTypeOfCoreExpr ce) (
      coreExprToWeakExpr ce >>= fun we =>
        addErrorMessage ("WeakExpr: " +++ we)
          ((addErrorMessage ("CoreType of WeakExpr: " +++ coreTypeOfCoreExpr (weakExprToCoreExpr we))
            ((weakTypeOfWeakExpr we) >>= fun t =>
              (addErrorMessage ("WeakType: " +++ t)
                ((weakTypeToTypeOfKind φ t ★) >>= fun τ =>
                  addErrorMessage ("HaskType: " +++ τ)
                  ((weakExprToStrongExpr Γ Δ φ ψ ξ (fun _ => true) τ nil we) >>= fun e =>
                        (let haskProof := @expr2proof _ _ _ _ _ _ e
                          in (* insert HaskProof-to-HaskProof manipulations here *)
                   (unFresh (@proof2expr nat _ FreshNat _ _ _ _ (fun _ => Prelude_error "unbound unique") _ haskProof))
                  >>= fun e' => Error (@toString _ (ExprToString _ _ _ _) (projT2 e'))
(*
                  >>= fun e' =>
                    Prelude_error (@toString _ (@ExprToString nat _ _ _ _ _ _) (projT2 e'))
  *)                  
)
)))))))).
(*                    Error "X").*)
(*
                   strongExprToWeakExpr hetmet_brak hetmet_esc mkWeakTypeVar mkWeakCoerVar mkWeakExprVar uniqueSupply
                   (projT2 e')
                         INil
                         >>= fun q => Error (toString q)
                  ))))))))).
*)
*)

    Definition coreToCoreExpr' (ce:@CoreExpr CoreVar) : ???(@CoreExpr CoreVar) :=
      addErrorMessage ("input CoreSyn: " +++ ce)
      (addErrorMessage ("input CoreType: " +++ coreTypeOfCoreExpr ce) (
        coreExprToWeakExpr ce >>= fun we =>
          addErrorMessage ("WeakExpr: " +++ we)
            ((addErrorMessage ("CoreType of WeakExpr: " +++ coreTypeOfCoreExpr (weakExprToCoreExpr we))
              ((weakTypeOfWeakExpr we) >>= fun t =>
                (addErrorMessage ("WeakType: " +++ t)
                  ((weakTypeToTypeOfKind φ t ★) >>= fun τ =>

                    ((weakExprToStrongExpr Γ Δ φ ψ ξ (fun _ => true) τ nil we) >>= fun e =>

                      (addErrorMessage ("HaskStrong...")
                        (let haskProof := @expr2proof _ _ _ _ _ _ e
                         in (* insert HaskProof-to-HaskProof manipulations here *)
                         OK ((@proof2expr nat _ FreshNat _ _ _ _ (fun _ => Prelude_error "unbound unique") _ haskProof) O)
                         >>= fun e' =>
                           (snd e') >>= fun e'' =>
                         strongExprToWeakExpr hetmet_brak hetmet_esc mkWeakTypeVar mkWeakCoerVar mkWeakExprVar uniqueSupply
                           (projT2 e'') INil
                         >>= fun q =>
                           OK (weakExprToCoreExpr q)
                    )))))))))).

    Definition coreToCoreExpr (ce:@CoreExpr CoreVar) : (@CoreExpr CoreVar) :=
      match coreToCoreExpr' ce with
        | OK x    => x
        | Error s => Prelude_error s
      end.
  
    Definition coreToCoreBind (binds:@CoreBind CoreVar) : @CoreBind CoreVar :=
      match binds with
        | CoreNonRec v e => CoreNonRec v (coreToCoreExpr e)
        | CoreRec    lbe => CoreRec (map (fun ve => match ve with (v,e) => (v,coreToCoreExpr e) end) lbe)
      end.
  
    Definition coqPassCoreToCore' (lbinds:list (@CoreBind CoreVar)) : list (@CoreBind CoreVar) :=
      map coreToCoreBind lbinds.

  End CoreToCore.

  Definition coqPassCoreToCore
    (hetmet_brak  : CoreVar)
    (hetmet_esc   : CoreVar)
    (uniqueSupply : UniqSupply)
    (lbinds:list (@CoreBind CoreVar)) : list (@CoreBind CoreVar) :=
    match coreVarToWeakVar hetmet_brak with
      | WExprVar hetmet_brak' => match coreVarToWeakVar hetmet_esc with
                                   | WExprVar hetmet_esc' => coqPassCoreToCore' hetmet_brak' hetmet_esc' uniqueSupply lbinds
                                   | _ => Prelude_error "IMPOSSIBLE"
                                 end
      | _ => Prelude_error "IMPOSSIBLE"
    end.

End core2proof.
