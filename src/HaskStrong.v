(*********************************************************************************************************************************)
(* HaskStrong: a dependently-typed version of CoreSyn                                                                            *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import HaskKinds.
Require Import HaskCoreTypes.
Require Import HaskLiterals.
Require Import HaskTyCons.
Require Import HaskStrongTypes.
Require Import HaskWeakVars.
Require Import HaskCoreVars.

Section HaskStrong.

  (* any type with decidable equality may be used to represent value variables *)
  Context `{EQD_VV:EqDecidable VV}.

  (* a StrongCaseBranchWithVVs contains all the data found in a case branch except the expression itself *)
  Record StrongCaseBranchWithVVs {tc:TyCon}{Γ}{atypes:IList _ (HaskType Γ) (tyConKind tc)}{sac:@StrongAltCon tc} :=
  { scbwv_exprvars          :  vec VV (sac_numExprVars sac)
  ; scbwv_exprvars_distinct :  distinct (vec2list scbwv_exprvars)
  ; scbwv_varstypes         := vec_zip scbwv_exprvars (sac_types sac Γ atypes)
  ; scbwv_xi                := fun ξ lev =>  update_xi (weakLT'○ξ) (weakL' lev) (vec2list scbwv_varstypes)
  }.
  Implicit Arguments StrongCaseBranchWithVVs [[Γ]].

  Inductive Expr : forall Γ (Δ:CoercionEnv Γ), (VV -> LeveledHaskType Γ ★) -> HaskType Γ ★ -> HaskLevel Γ -> Type :=

  (* an "EGlobal" is any variable which is free in the expression which was passed to -fcoqpass (ie bound outside it) *)
  | EGlobal: forall Γ Δ ξ   (g:Global Γ) v lev,                                                      Expr Γ Δ ξ (g v) lev

  | EVar   : ∀ Γ Δ ξ ev,                                                                Expr Γ Δ ξ (unlev (ξ ev)) (getlev (ξ ev))
  | ELit   : ∀ Γ Δ ξ lit   l,                                                                        Expr Γ Δ ξ (literalType lit) l
  | EApp   : ∀ Γ Δ ξ t1 t2 l,        Expr Γ Δ ξ (t2--->t1) l   -> Expr Γ Δ ξ t2 l         -> Expr Γ Δ ξ (t1) l
  | ELam   : ∀ Γ Δ ξ t1 t2 l ev,              Expr Γ Δ (update_xi ξ l ((ev,t1)::nil)) t2 l       -> Expr Γ Δ ξ (t1--->t2) l
  | ELet   : ∀ Γ Δ ξ tv t  l ev,Expr Γ Δ ξ  tv l ->Expr Γ Δ (update_xi ξ l ((ev,tv)::nil)) t l  -> Expr Γ Δ ξ t l
  | EEsc   : ∀ Γ Δ ξ ec t  l,     Expr Γ Δ ξ  (<[ ec |- t ]>)  l                                  -> Expr Γ Δ ξ t (ec::l)
  | EBrak  : ∀ Γ Δ ξ ec t  l,     Expr Γ Δ ξ t  (ec::l)                                         -> Expr Γ Δ ξ (<[ ec |- t ]>) l
  | ECast  : forall Γ Δ ξ t1 t2 (γ:HaskCoercion Γ Δ (t1 ∼∼∼ t2)) l, Expr Γ Δ ξ t1 l             -> Expr Γ Δ ξ t2 l
  | ENote  : ∀ Γ Δ ξ t l, Note                      -> Expr Γ Δ ξ t l                               -> Expr Γ Δ ξ t l
  | ETyApp : ∀ Γ Δ κ σ τ ξ l,                    Expr Γ Δ ξ (HaskTAll κ σ) l                   -> Expr Γ Δ ξ (substT σ τ) l
  | ECoLam : forall Γ Δ κ σ (σ₁ σ₂:HaskType Γ κ) ξ l, Expr Γ (σ₁∼∼∼σ₂::Δ) ξ σ l    -> Expr Γ Δ ξ (σ₁∼∼σ₂    ⇒ σ) l
  | ECoApp : forall Γ Δ κ (σ₁ σ₂:HaskType Γ κ) (γ:HaskCoercion Γ Δ (σ₁∼∼∼σ₂)) σ ξ l, Expr Γ Δ ξ (σ₁ ∼∼ σ₂ ⇒ σ) l  -> Expr Γ Δ ξ σ l
  | ETyLam : ∀ Γ Δ ξ κ σ l,
    Expr (κ::Γ) (weakCE Δ) (weakLT○ξ) (HaskTApp (weakF σ) (FreshHaskTyVar _)) (weakL l)-> Expr Γ Δ ξ (HaskTAll κ σ) l
  | ECase    : forall Γ Δ ξ l tc tbranches atypes,
               Expr Γ Δ ξ (caseType tc atypes) l ->
               Tree ??{ sac : _
                    & { scb : StrongCaseBranchWithVVs tc atypes sac
                    &         Expr (sac_gamma sac Γ)
                                   (sac_delta sac Γ atypes (weakCK'' Δ))
                                   (scbwv_xi scb ξ l)
                                   (weakT' tbranches)
                                   (weakL' l) } } ->
               Expr Γ Δ ξ tbranches l

  | ELetRec  : ∀ Γ Δ ξ l τ vars,
    distinct (leaves (mapOptionTree (@fst _ _) vars)) ->
    let ξ' := update_xi ξ l (leaves vars) in
    ELetRecBindings Γ Δ ξ'   l vars ->
    Expr            Γ Δ ξ' τ l ->
    Expr            Γ Δ ξ  τ l

  (* can't avoid having an additional inductive: it is a tree of Expr's, each of whose ξ depends on the type of the entire tree *)
  with ELetRecBindings : ∀ Γ, CoercionEnv Γ -> (VV -> LeveledHaskType Γ ★) -> HaskLevel Γ -> Tree ??(VV*HaskType Γ ★) -> Type :=
  | ELR_nil    : ∀ Γ Δ ξ l  ,                                                                 ELetRecBindings Γ Δ ξ l []
  | ELR_leaf   : ∀ Γ Δ ξ l v t,                                        Expr Γ Δ ξ  t  l    -> ELetRecBindings Γ Δ ξ l [(v,t)]
  | ELR_branch : ∀ Γ Δ ξ l t1 t2, ELetRecBindings Γ Δ ξ l t1 -> ELetRecBindings Γ Δ ξ l t2 -> ELetRecBindings Γ Δ ξ l (t1,,t2)
  .

  Context {ToStringVV:ToString VV}.
  Context {ToLatexVV:ToLatex VV}.
  Fixpoint exprToString {Γ}{Δ}{ξ}{τ}{l}(exp:Expr Γ Δ ξ τ l) : string :=
    match exp with
    | EVar  Γ' _ ξ' ev              => "var."+++ toString ev
    | EGlobal Γ' _ ξ'   g v _       => "global." +++ toString (g:CoreVar)
    | ELam  Γ'   _ _ tv _ _ cv e    => "\("+++ toString cv +++":t) -> "+++ exprToString e
    | ELet  Γ' _ _ t _ _ ev e1 e2   => "let "+++toString ev+++" = "+++exprToString e1+++" in "+++exprToString e2
    | ELit  _ _ _ lit _             => "lit."+++toString lit
    | EApp  Γ' _ _ _ _ _ e1 e2      => "("+++exprToString e1+++")("+++exprToString e2+++")"
    | EEsc  Γ' _ _ ec t _ e         => "~~("+++exprToString e+++")"
    | EBrak Γ' _ _ ec t _ e         => "<["+++exprToString e+++"]>"
    | ENote _ _ _ _ n _ e           => "note."+++exprToString e
    | ETyApp  Γ Δ κ σ τ ξ l       e => "("+++exprToString e+++")@("+++toString τ+++")"
    | ECoApp Γ Δ κ σ₁ σ₂ γ σ ξ l e  => "("+++exprToString e+++")~(co)"
    | ECast Γ Δ ξ t1 t2 γ l e       => "cast ("+++exprToString e+++"):t2"
    | ETyLam _ _ _ k _ _ e          => "\@_ ->"+++ exprToString e
    | ECoLam Γ Δ κ σ σ₁ σ₂ ξ l e    => "\~_ ->"+++ exprToString e
    | ECase Γ Δ ξ l tc branches atypes escrut alts => "case " +++ exprToString escrut +++ " of FIXME"
    | ELetRec _ _ _ _ _ vars vu elrb e => "letrec FIXME in " +++ exprToString e
    end.
  Instance ExprToString Γ Δ ξ τ l : ToString (Expr Γ Δ ξ τ l) := { toString := exprToString }.

End HaskStrong.
Implicit Arguments StrongCaseBranchWithVVs [[Γ]].
