(*********************************************************************************************************************************)
(* HaskStrong: a dependently-typed version of CoreSyn                                                                            *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import HaskKinds.
Require Import HaskWeakVars.
Require Import HaskCoreTypes.
Require Import HaskCoreLiterals.
Require Import HaskStrongTypes.

Section HaskStrong.

  (* any type with decidable equality may be used to represent value variables *)
  Context `{EQD_VV:EqDecidable VV}.

  (* a StrongCaseBranchWithVVs contains all the data found in a case branch except the expression itself *)

  Record StrongCaseBranchWithVVs {tc:TyCon}{Γ}{sac:@StrongAltCon tc}{atypes:IList _ (HaskType Γ) (tyConKind sac)} :=
  { scbwv_sac       := sac
  ; scbwv_exprvars  :  vec VV (sac_numExprVars scbwv_sac)
  ; scbwv_varstypes := vec_zip scbwv_exprvars (sac_types scbwv_sac Γ atypes)
  ; scbwv_ξ         := fun ξ lev =>  update_ξ (weakLT'○ξ) (vec2list
                                        (vec_map (fun x => ((fst x),(snd x @@ weakL' lev))) scbwv_varstypes))
  }.
  Implicit Arguments StrongCaseBranchWithVVs [[Γ]].
  Coercion scbwv_sac : StrongCaseBranchWithVVs >-> StrongAltCon.

  Inductive Expr : forall Γ (Δ:CoercionEnv Γ), (VV -> LeveledHaskType Γ ★) -> LeveledHaskType Γ ★ -> Type :=
  | EVar   : ∀ Γ Δ ξ ev,                                                                             Expr Γ Δ ξ (ξ ev)
  | ELit   : ∀ Γ Δ ξ lit   l,                                                                        Expr Γ Δ ξ (literalType lit@@l)
  | EApp   : ∀ Γ Δ ξ t1 t2 l,        Expr Γ Δ ξ (t2--->t1 @@ l)   -> Expr Γ Δ ξ (t2 @@ l)         -> Expr Γ Δ ξ (t1 @@ l)
  | ELam   : ∀ Γ Δ ξ t1 t2 l ev,              Expr Γ Δ (update_ξ ξ ((ev,t1@@l)::nil)) (t2@@l)     -> Expr Γ Δ ξ (t1--->t2@@l)
  | ELet   : ∀ Γ Δ ξ tv t  l ev,Expr Γ Δ ξ (tv@@l)->Expr Γ Δ (update_ξ ξ ((ev,tv@@l)::nil))(t@@l) -> Expr Γ Δ ξ (t@@l)
  | EEsc   : ∀ Γ Δ ξ ec t  l,     Expr Γ Δ ξ (<[ ec |- t ]> @@ l)                                 -> Expr Γ Δ ξ (t @@ (ec::l))
  | EBrak  : ∀ Γ Δ ξ ec t  l,     Expr Γ Δ ξ (t @@ (ec::l))                                       -> Expr Γ Δ ξ (<[ ec |- t ]> @@ l)
  | ECast  : forall Γ Δ ξ t1 t2 (γ:HaskCoercion Γ Δ (t1 ∼∼∼ t2)) l,
    Expr Γ Δ ξ (t1 @@ l)                        -> Expr Γ Δ ξ (t2 @@ l)
  | ENote  : ∀ Γ Δ ξ t, Note                      -> Expr Γ Δ ξ t                                 -> Expr Γ Δ ξ t
  | ETyApp : ∀ Γ Δ κ σ τ ξ l,                    Expr Γ Δ ξ (HaskTAll κ σ @@ l)                   -> Expr Γ Δ ξ (substT σ τ @@ l)
  | ECoLam : forall Γ Δ κ σ (σ₁ σ₂:HaskType Γ κ) ξ l,
    Expr Γ (σ₁∼∼∼σ₂::Δ) ξ (σ @@ l)    -> Expr Γ Δ ξ (σ₁∼∼σ₂    ⇒ σ @@ l)
  | ECoApp : forall Γ Δ κ (σ₁ σ₂:HaskType Γ κ) (γ:HaskCoercion Γ Δ (σ₁∼∼∼σ₂)) σ ξ l,
    Expr Γ Δ ξ (σ₁ ∼∼ σ₂ ⇒ σ @@ l)            -> Expr Γ Δ ξ (σ        @@l)
  | ETyLam : ∀ Γ Δ ξ κ σ l,
    Expr (κ::Γ) (weakCE Δ) (weakLT○ξ) (HaskTApp (weakF σ) (FreshHaskTyVar _)@@(weakL l))-> Expr Γ Δ ξ (HaskTAll κ σ @@ l)
  | ECase    : forall Γ Δ ξ l tc tbranches sac atypes,
               Expr Γ Δ ξ (caseType tc atypes @@ l) ->
               Tree ??{ scb : StrongCaseBranchWithVVs tc sac atypes
                            & Expr (sac_Γ scb Γ)
                                   (sac_Δ scb Γ atypes (weakCK'' Δ))
                                   (scbwv_ξ scb ξ l)
                                   (weakLT' (tbranches@@l)) } ->
               Expr Γ Δ ξ (tbranches @@ l)

  | ELetRec  : ∀ Γ Δ ξ l τ vars, let ξ' := update_ξ ξ (map (fun x => ((fst x),(snd x @@ l))) (leaves vars)) in
    ELetRecBindings Γ Δ ξ'     l vars ->
    Expr            Γ Δ ξ' (τ@@l) ->
    Expr            Γ Δ ξ  (τ@@l)

  (* can't avoid having an additional inductive: it is a tree of Expr's, each of whose ξ depends on the type of the entire tree *)
  with ELetRecBindings : ∀ Γ, CoercionEnv Γ -> (VV -> LeveledHaskType Γ ★) -> HaskLevel Γ -> Tree ??(VV*HaskType Γ ★) -> Type :=
  | ELR_nil    : ∀ Γ Δ ξ l  ,                                                                 ELetRecBindings Γ Δ ξ l []
  | ELR_leaf   : ∀ Γ Δ ξ t l v,                                        Expr Γ Δ ξ (t @@ l) -> ELetRecBindings Γ Δ ξ l [(v,t)]
  | ELR_branch : ∀ Γ Δ ξ l t1 t2, ELetRecBindings Γ Δ ξ l t1 -> ELetRecBindings Γ Δ ξ l t2 -> ELetRecBindings Γ Δ ξ l (t1,,t2)
  .

End HaskStrong.
Implicit Arguments StrongCaseBranchWithVVs [[Γ]].
