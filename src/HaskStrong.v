(*********************************************************************************************************************************)
(* HaskStrong: a dependently-typed version of CoreSyn                                                                            *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import HaskGeneral.
Require Import HaskLiterals.
Require Import HaskStrongTypes.

Section HaskStrong.

  (* any type with decidable equality may be used to represent value variables *)
  Context `{EQD_VV:EqDecidable VV}.

  (* a ExprCaseBranch contains all the data found in a case branch except the expression itself *)
  Record ExprCaseBranch {n}{tc:TyCon n}{Γ}{atypes:vec (HaskType Γ) n} :=
  { cbi_sacic     :  @StrongAltConInContext n tc Γ atypes
  ; cbi_vars      :  vec VV (tagNumValVars (cbi_tag cbi_sacic))
  ; cbi_varstypes := vec2list (vec_zip cbi_vars (cbi_types cbi_sacic))
  }.
  Implicit Arguments ExprCaseBranch [[n][Γ]].
  Coercion cbi_sacic : ExprCaseBranch >-> StrongAltConInContext.

  Inductive Expr : forall Γ (Δ:CoercionEnv Γ), (VV -> LeveledHaskType Γ) -> LeveledHaskType Γ -> Type :=
  | EVar   : ∀ Γ Δ ξ ev,                                                                             Expr Γ Δ ξ (ξ ev)
  | ELit   : ∀ Γ Δ ξ lit   l,                                                                        Expr Γ Δ ξ (literalType lit@@l)
  | EApp   : ∀ Γ Δ ξ t1 t2 l,        Expr Γ Δ ξ (t2--->t1 @@ l)   -> Expr Γ Δ ξ (t2 @@ l)         -> Expr Γ Δ ξ (t1 @@ l)
  | ELam   : ∀ Γ Δ ξ t1 t2 l ev, Γ ⊢ᴛy t1:★ ->Expr Γ Δ (update_ξ ξ ((ev,t1@@l)::nil)) (t2@@l)     -> Expr Γ Δ ξ (t1--->t2@@l)
  | ELet   : ∀ Γ Δ ξ tv t  l ev,Expr Γ Δ ξ (tv@@l)->Expr Γ Δ (update_ξ ξ ((ev,tv@@l)::nil))(t@@l) -> Expr Γ Δ ξ (t@@l)
  | EEsc   : ∀ Γ Δ ξ ec t  l,     Expr Γ Δ ξ (<[ ec |- t ]> @@ l)                                 -> Expr Γ Δ ξ (t @@ (ec::l))
  | EBrak  : ∀ Γ Δ ξ ec t  l,     Expr Γ Δ ξ (t @@ (ec::l))                                       -> Expr Γ Δ ξ (<[ ec |- t ]> @@ l)
  | ECast  : ∀ Γ Δ ξ γ t1 t2 l, Δ ⊢ᴄᴏ γ : t1 ∼ t2 ->  Expr Γ Δ ξ (t1 @@ l)                        -> Expr Γ Δ ξ (t2 @@ l)
  | ENote  : ∀ Γ Δ ξ t, Note                      -> Expr Γ Δ ξ t                                 -> Expr Γ Δ ξ t
  | ETyApp : ∀ Γ Δ κ σ τ ξ l,     Γ ⊢ᴛy τ : κ -> Expr Γ Δ ξ (HaskTAll κ σ @@ l)                   -> Expr Γ Δ ξ (substT σ τ @@ l)
  | ECoLam : ∀ Γ Δ κ σ σ₁ σ₂ ξ l,   Γ ⊢ᴛy σ₁:κ -> Γ ⊢ᴛy σ₂:κ -> Expr Γ (σ₁∼∼∼σ₂::Δ) ξ (σ @@ l)    -> Expr Γ Δ ξ (σ₁∼∼σ₂ :κ ⇒ σ @@ l)
  | ECoApp : ∀ Γ Δ κ γ σ₁ σ₂ σ ξ l, Δ ⊢ᴄᴏ γ  : σ₁∼σ₂ -> Expr Γ Δ ξ (σ₁ ∼∼ σ₂ : κ ⇒ σ @@ l)        -> Expr Γ Δ ξ (σ        @@l)
  | ETyLam : ∀ Γ Δ ξ κ σ l,
    Expr (κ::Γ) (weakCE Δ) (weakLT○ξ) (HaskTApp (weakF σ) (FreshHaskTyVar _)@@(weakL l))-> Expr Γ Δ ξ (HaskTAll κ σ @@ l)

  | ECase    : forall Γ Δ ξ l n (tc:TyCon n) atypes tbranches,
               Expr Γ Δ ξ (caseType tc atypes @@ l) ->
               Tree ??{ scb : ExprCaseBranch tc atypes
                            & Expr (cbi_Γ scb) (cbi_Δ scb) (update_ξ (weakLT'○ξ) (cbi_varstypes scb)) (weakLT' (tbranches@@l)) } ->
               Expr Γ Δ ξ (tbranches @@ l)

  | ELetRec  : ∀ Γ Δ ξ l τ vars, let ξ' := update_ξ ξ (map (fun x => ((fst x),(snd x @@ l))) (leaves vars)) in
    ELetRecBindings Γ Δ ξ'     l vars ->
    Expr            Γ Δ ξ' (τ@@l) ->
    Expr            Γ Δ ξ  (τ@@l)

  (* can't avoid having an additional inductive: it is a tree of Expr's, each of whose ξ depends on the type of the entire tree *)
  with ELetRecBindings : forall Γ (Δ:CoercionEnv Γ), (VV -> LeveledHaskType Γ) -> HaskLevel Γ -> Tree ??(VV*HaskType Γ) -> Type :=
  | ELR_nil    : ∀ Γ Δ ξ l  ,                                                                 ELetRecBindings Γ Δ ξ l []
  | ELR_leaf   : ∀ Γ Δ ξ t l v,                                        Expr Γ Δ ξ (t @@ l) -> ELetRecBindings Γ Δ ξ l [(v,t)]
  | ELR_branch : ∀ Γ Δ ξ l t1 t2, ELetRecBindings Γ Δ ξ l t1 -> ELetRecBindings Γ Δ ξ l t2 -> ELetRecBindings Γ Δ ξ l (t1,,t2)
  .

End HaskStrong.
