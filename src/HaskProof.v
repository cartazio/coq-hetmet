(*********************************************************************************************************************************)
(* HaskProof:                                                                                                                    *)
(*                                                                                                                               *)
(*    Natural Deduction proofs of the well-typedness of a Haskell term.  Proofs use explicit structural rules (Gentzen-style)    *)
(*    and are in System FC extended with modal types indexed by Taha-Nielsen environment classifiers (λ^α)                       *)
(*                                                                                                                               *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import NaturalDeduction.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import HaskKinds.
Require Import HaskCoreTypes.
Require Import HaskLiteralsAndTyCons.
Require Import HaskStrongTypes.
Require Import HaskWeakVars.

(* A judgment consists of an environment shape (Γ and Δ) and a pair of trees of leveled types (the antecedent and succedent) valid
 * in any context of that shape.  Notice that the succedent contains a tree of types rather than a single type; think
 * of [ T1 |- T2 ] as asserting that a letrec with branches having types corresponding to the leaves of T2 is well-typed
 * in environment T1.  This subtle distinction starts to matter when we get into substructural (linear, affine, ordered, etc)
 * types *)
Inductive Judg  :=
  mkJudg :
  forall Γ:TypeEnv,
  forall Δ:CoercionEnv Γ,
  Tree ??(LeveledHaskType Γ ★) ->
  Tree ??(LeveledHaskType Γ ★) ->
  Judg.
  Notation "Γ > Δ > a '|-' s" := (mkJudg Γ Δ a s) (at level 52, Δ at level 50, a at level 52, s at level 50).

(* A Uniform Judgment (UJudg) has its environment as a type index; we'll use these to distinguish proofs that have a single,
 * uniform context throughout the whole proof.  Such proofs are important because (1) we can do left and right context
 * expansion on them (see rules RLeft and RRight) and (2) they will form the fiber categories of our fibration later on *)
Inductive UJudg (Γ:TypeEnv)(Δ:CoercionEnv Γ) :=
  mkUJudg :
  Tree ??(LeveledHaskType Γ ★) ->
  Tree ??(LeveledHaskType Γ ★) ->
  UJudg Γ Δ.
  Notation "Γ >> Δ > a '|-' s" := (mkUJudg Γ Δ a s) (at level 52, Δ at level 50, a at level 52, s at level 50).
  Definition ext_tree_left  {Γ}{Δ}  := (fun ctx (j:UJudg Γ Δ) => match j with mkUJudg t s => mkUJudg Γ Δ (ctx,,t) s end).
  Definition ext_tree_right {Γ}{Δ}  := (fun ctx (j:UJudg Γ Δ) => match j with mkUJudg t s => mkUJudg Γ Δ (t,,ctx) s end).

(* we can turn a UJudg into a Judg by simply internalizing the index *)
Definition UJudg2judg {Γ}{Δ}(ej:@UJudg Γ Δ) : Judg :=
  match ej with mkUJudg t s => Γ > Δ > t |- s end.
  Coercion UJudg2judg : UJudg >-> Judg.

(* information needed to define a case branch in a HaskProof *)
Record ProofCaseBranch {tc:TyCon}{Γ}{Δ}{lev}{branchtype : HaskType Γ ★}{avars} :=
{ pcb_scb            :  @StrongAltCon tc
; pcb_freevars       :  Tree ??(LeveledHaskType Γ ★)
; pcb_judg           := sac_Γ pcb_scb Γ > sac_Δ pcb_scb Γ avars (map weakCK' Δ)
                > (mapOptionTree weakLT' pcb_freevars),,(unleaves (map (fun t => t@@weakL' lev)
                  (vec2list (sac_types pcb_scb Γ avars))))
                |- [weakLT' (branchtype @@ lev)]
}.
Coercion pcb_scb : ProofCaseBranch >-> StrongAltCon.
Implicit Arguments ProofCaseBranch [ ].

(* Figure 3, production $\vdash_E$, Uniform rules *)
Inductive URule {Γ}{Δ} : Tree ??(UJudg Γ Δ) -> Tree ??(UJudg Γ Δ) -> Type :=
| RCanL   : ∀ t a        ,                          URule  [Γ>>Δ>    [],,a   |- t         ]      [Γ>>Δ>       a   |- t           ]
| RCanR   : ∀ t a        ,                          URule  [Γ>>Δ>    a,,[]   |- t         ]      [Γ>>Δ>       a   |- t           ]
| RuCanL  : ∀ t a        ,                          URule  [Γ>>Δ>       a    |- t         ]      [Γ>>Δ>  [],,a    |- t           ]
| RuCanR  : ∀ t a        ,                          URule  [Γ>>Δ>       a    |- t         ]      [Γ>>Δ>  a,,[]    |- t           ]
| RAssoc  : ∀ t a b c    ,                          URule  [Γ>>Δ>a,,(b,,c)   |- t         ]      [Γ>>Δ>(a,,b),,c  |- t           ]
| RCossa  : ∀ t a b c    ,                          URule  [Γ>>Δ>(a,,b),,c   |- t         ]      [Γ>>Δ> a,,(b,,c) |- t           ]
| RLeft   : ∀ h c x      ,             URule h c -> URule (mapOptionTree (ext_tree_left  x) h) (mapOptionTree (ext_tree_left  x) c)
| RRight  : ∀ h c x      ,             URule h c -> URule (mapOptionTree (ext_tree_right x) h) (mapOptionTree (ext_tree_right x) c)
| RExch   : ∀ t a b      ,                          URule  [Γ>>Δ>   (b,,a)   |- t         ]      [Γ>>Δ>  (a,,b)   |- t           ]
| RWeak   : ∀ t a        ,                          URule  [Γ>>Δ>       []   |- t         ]      [Γ>>Δ>       a   |- t           ]
| RCont   : ∀ t a        ,                          URule  [Γ>>Δ>  (a,,a)    |- t         ]      [Γ>>Δ>       a   |- t           ].


(* Figure 3, production $\vdash_E$, all rules *)
Inductive Rule : Tree ??Judg -> Tree ??Judg -> Type :=

| RURule  : ∀ Γ Δ h c,                  @URule Γ Δ h c -> Rule (mapOptionTree UJudg2judg h) (mapOptionTree UJudg2judg c)

(* λ^α rules *)
| RBrak : ∀ Γ Δ t v Σ l,                              Rule [Γ > Δ > Σ      |- [t  @@ (v::l) ]]   [Γ > Δ > Σ     |- [<[v|-t]>   @@l]]
| REsc  : ∀ Γ Δ t v Σ l,                              Rule [Γ > Δ > Σ      |- [<[v|-t]> @@ l]]   [Γ > Δ > Σ     |- [t  @@ (v::l)  ]]

(* Part of GHC, but not explicitly in System FC *)
| RNote   : ∀ Γ Δ Σ τ l,          Note ->             Rule  [Γ > Δ > Σ |- [τ @@ l]] [Γ > Δ > Σ |- [τ @@ l]]
| RLit    : ∀ Γ Δ v       l,                          Rule  [                                ]   [Γ > Δ > []|- [literalType v @@ l]]

(* SystemFC rules *)
| RVar    : ∀ Γ Δ σ       l,                          Rule [                                 ]   [Γ>Δ> [σ@@l]   |- [σ          @@l]]
| RGlobal : ∀ Γ Δ τ       l,   WeakExprVar ->         Rule [                                 ]   [Γ>Δ>     []   |- [τ          @@l]]
| RLam    : forall Γ Δ Σ (tx:HaskType Γ ★) te l,      Rule [Γ>Δ> Σ,,[tx@@l]|- [te@@l]        ]   [Γ>Δ>    Σ     |- [tx--->te   @@l]]
| RCast   : forall Γ Δ Σ (σ₁ σ₂:HaskType Γ ★) l,
HaskCoercion Γ Δ (σ₁∼∼∼σ₂) ->
 Rule [Γ>Δ> Σ         |- [σ₁@@l]         ]   [Γ>Δ>    Σ     |- [σ₂          @@l]]
| RBindingGroup  : ∀ Γ Δ Σ₁ Σ₂ τ₁ τ₂ ,   Rule ([Γ > Δ > Σ₁ |- τ₁ ],,[Γ > Δ > Σ₂ |- τ₂ ])         [Γ>Δ>  Σ₁,,Σ₂  |- τ₁,,τ₂          ]
| RApp           : ∀ Γ Δ Σ₁ Σ₂ tx te l,  Rule ([Γ>Δ> Σ₁       |- [tx--->te @@l]],,[Γ>Δ> Σ₂ |- [tx@@l]])  [Γ>Δ> Σ₁,,Σ₂ |- [te   @@l]]
| RLet           : ∀ Γ Δ Σ₁ Σ₂ σ₁ σ₂ l,  Rule ([Γ>Δ> Σ₁,,[σ₂@@l] |- [σ₁@@l] ],,[Γ>Δ> Σ₂ |- [σ₂@@l]])     [Γ>Δ> Σ₁,,Σ₂ |- [σ₁   @@l]]
| REmptyGroup    : ∀ Γ Δ ,               Rule [] [Γ > Δ > [] |- [] ]
| RAppT   : forall Γ Δ Σ κ σ (τ:HaskType Γ κ) l,      Rule [Γ>Δ> Σ   |- [HaskTAll κ σ @@l]]      [Γ>Δ>    Σ     |- [substT σ τ @@l]]
| RAbsT   : ∀ Γ Δ Σ κ σ   l,
  Rule [(κ::Γ)> (weakCE Δ)    >   mapOptionTree weakLT Σ |- [ HaskTApp (weakF σ) (FreshHaskTyVar _) @@ (weakL l)]]
       [Γ>Δ            >    Σ     |- [HaskTAll κ σ   @@ l]]
| RAppCo  : forall Γ Δ Σ κ (σ₁ σ₂:HaskType Γ κ) (γ:HaskCoercion Γ Δ (σ₁∼∼∼σ₂)) σ l,
    Rule [Γ>Δ> Σ |- [σ₁∼∼σ₂ ⇒ σ@@l]] [Γ>Δ>    Σ     |- [σ        @@l]]
| RAbsCo  : forall Γ Δ Σ κ (σ₁ σ₂:HaskType Γ κ) σ l,
   Rule [Γ > ((σ₁∼∼∼σ₂)::Δ)            > Σ |- [σ @@ l]]
        [Γ > Δ >                         Σ |- [σ₁∼∼σ₂⇒ σ @@l]]
| RLetRec        : ∀ Γ Δ Σ₁ τ₁ τ₂, Rule [Γ > Δ > Σ₁,,τ₂ |- τ₁,,τ₂ ] [Γ > Δ > Σ₁ |- τ₁ ]
| RCase          : forall Γ Δ lev tc Σ avars tbranches
  (alts:Tree ??(@ProofCaseBranch tc Γ Δ lev tbranches avars)),
                   Rule
                       ((mapOptionTree pcb_judg alts),,
                        [Γ > Δ >                                              Σ |- [ caseType tc avars @@ lev ] ])
                        [Γ > Δ > (mapOptionTreeAndFlatten pcb_freevars alts),,Σ |- [ tbranches         @@ lev ] ]
.
Coercion RURule : URule >-> Rule.


(* A rule is considered "flat" if it is neither RBrak nor REsc *)
Inductive Rule_Flat : forall {h}{c}, Rule h c -> Prop :=
| Flat_RURule           : ∀ Γ Δ  h c r            ,  Rule_Flat (RURule Γ Δ  h c r)
| Flat_RNote            : ∀ Γ Δ Σ τ l n            ,  Rule_Flat (RNote Γ Δ Σ τ l n)
| Flat_RVar             : ∀ Γ Δ  σ               l,  Rule_Flat (RVar Γ Δ  σ         l)
| Flat_RLam             : ∀ Γ Δ  Σ tx te    q    ,  Rule_Flat (RLam Γ Δ  Σ tx te      q )
| Flat_RCast            : ∀ Γ Δ  Σ σ τ γ    q     ,  Rule_Flat (RCast Γ Δ  Σ σ τ γ    q )
| Flat_RAbsT            : ∀ Γ   Σ κ σ a    q    ,  Rule_Flat (RAbsT Γ   Σ κ σ a    q )
| Flat_RAppT            : ∀ Γ Δ  Σ κ σ τ    q    ,  Rule_Flat (RAppT Γ Δ  Σ κ σ τ    q )
| Flat_RAppCo           : ∀ Γ Δ  Σ σ₁ σ₂ σ γ q l,  Rule_Flat (RAppCo Γ Δ  Σ  σ₁ σ₂ σ γ  q l)
| Flat_RAbsCo           : ∀ Γ   Σ κ σ  σ₁ σ₂ q1 q2   , Rule_Flat (RAbsCo Γ   Σ κ σ  σ₁ σ₂  q1 q2   )
| Flat_RApp             : ∀ Γ Δ  Σ tx te   p     l,  Rule_Flat (RApp Γ Δ  Σ tx te   p l)
| Flat_RLet             : ∀ Γ Δ  Σ σ₁ σ₂   p     l,  Rule_Flat (RLet Γ Δ  Σ σ₁ σ₂   p l)
| Flat_RBindingGroup    : ∀ q a b c d e ,  Rule_Flat (RBindingGroup q a b c d e)
| Flat_RCase            : ∀ Σ Γ  T κlen κ θ l x  , Rule_Flat (RCase Σ Γ T κlen κ θ l x).

(* given a proof that uses only uniform rules, we can produce a general proof *)
Definition UND_to_ND Γ Δ h c : ND (@URule Γ Δ) h c -> ND Rule (mapOptionTree UJudg2judg h) (mapOptionTree UJudg2judg c)
  := @nd_map' _ (@URule Γ Δ ) _ Rule (@UJudg2judg Γ Δ ) (fun h c r => nd_rule (RURule _ _ h c r)) h c.

Lemma no_urules_with_empty_conclusion : forall Γ Δ c h, @URule Γ Δ c h -> h=[] -> False.
  intro.
  intro.
  induction 1; intros; inversion H.
  simpl in *;  destruct c; try destruct o;  simpl in *; try destruct u;  inversion H;  simpl in *;  apply IHX;  auto;  inversion H1.
  simpl in *;  destruct c; try destruct o;  simpl in *; try destruct u;  inversion H;  simpl in *;  apply IHX;  auto;  inversion H1.
  Qed.

Lemma no_rules_with_empty_conclusion : forall c h, @Rule c h -> h=[] -> False.
  intros.
  destruct X; try destruct c; try destruct o; simpl in *; try inversion H.
  apply no_urules_with_empty_conclusion in u.
  apply u.
  auto.
  Qed.

Lemma no_urules_with_multiple_conclusions : forall Γ Δ c h,
  @URule Γ Δ c h -> { h1:Tree ??(UJudg Γ Δ) & { h2:Tree ??(UJudg Γ Δ) & h=(h1,,h2) }} -> False.
  intro.
  intro.
  induction 1; intros.
  inversion X;inversion X0;inversion H;inversion X1;destruct c;try destruct o; inversion H2; apply IHX; exists c1;exists c2; auto.
  inversion X;inversion X0;inversion H;inversion X1;destruct c;try destruct o; inversion H2; apply IHX; exists c1;exists c2; auto.
  inversion X;inversion X0;inversion H;inversion X1;destruct c;try destruct o; inversion H2; apply IHX; exists c1;exists c2; auto.
  inversion X;inversion X0;inversion H;inversion X1;destruct c;try destruct o; inversion H2; apply IHX; exists c1;exists c2; auto.
  inversion X;inversion X0;inversion H;inversion X1;destruct c;try destruct o; inversion H2; apply IHX; exists c1;exists c2; auto.
  inversion X;inversion X0;inversion H;inversion X1;destruct c;try destruct o; inversion H2; apply IHX; exists c1;exists c2; auto.

  apply IHX.
  destruct X0. destruct s. destruct c; try destruct o; try destruct u; simpl in *.
    inversion e.
    inversion e.
    exists c1. exists c2. auto.

  apply IHX.
  destruct X0. destruct s. destruct c; try destruct o; try destruct u; simpl in *.
    inversion e.
    inversion e.
    exists c1. exists c2. auto.

  inversion X;inversion X0;inversion H;inversion X1;destruct c;try destruct o; inversion H2; apply IHX; exists c1;exists c2; auto.
  inversion X;inversion X0;inversion H;inversion X1;destruct c;try destruct o; inversion H2; apply IHX; exists c1;exists c2; auto.
  inversion X;inversion X0;inversion H;inversion X1;destruct c;try destruct o; inversion H2; apply IHX; exists c1;exists c2; auto.
  Qed.

Lemma no_rules_with_multiple_conclusions : forall c h,
  Rule c h -> { h1:Tree ??Judg & { h2:Tree ??Judg & h=(h1,,h2) }} -> False.
  intros.
  destruct X; try destruct c; try destruct o; simpl in *; try inversion H;
    try apply no_urules_with_empty_conclusion in u; try apply u.
    destruct X0; destruct s; inversion e.
    auto.
    apply (no_urules_with_multiple_conclusions _ _ h (c1,,c2)) in u. inversion u. exists c1. exists c2. auto.
    destruct X0; destruct s; inversion e.
    destruct X0; destruct s; inversion e.
    destruct X0; destruct s; inversion e.
    destruct X0; destruct s; inversion e.
    destruct X0; destruct s; inversion e.
    destruct X0; destruct s; inversion e.
    destruct X0; destruct s; inversion e.
    destruct X0; destruct s; inversion e.
    destruct X0; destruct s; inversion e.
    destruct X0; destruct s; inversion e.
    destruct X0; destruct s; inversion e.
    destruct X0; destruct s; inversion e.
    destruct X0; destruct s; inversion e.
    destruct X0; destruct s; inversion e.
    destruct X0; destruct s; inversion e.
    destruct X0; destruct s; inversion e.
    destruct X0; destruct s; inversion e.
    destruct X0; destruct s; inversion e.
    Qed.

Lemma systemfc_all_rules_one_conclusion : forall h c1 c2 (r:Rule h (c1,,c2)), False.
  intros.
  eapply no_rules_with_multiple_conclusions.
  apply r.
  exists c1.
  exists c2.
  auto.
  Qed.


