(*********************************************************************************************************************************)
(* HaskStrongTypes: representation of types and coercions for HaskStrong                                                         *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import HaskGeneral.
Require Import HaskLiterals.

(* types prefixed with "Raw" are NOT binder-polymorphic; they have had their PHOAS parameter instantiated already *)
Section Raw.

  (* TV is the PHOAS type which stands for type variables of System FC *)
  Context {TV:Type}.

  (* Figure 7: ρ, σ, τ, ν *)
  Inductive RawHaskType  : Type :=
  | TVar           : TV                                                     -> RawHaskType   (* a        *)
  | TCon           : ∀n, TyCon n                                            -> RawHaskType   (* T        *)
  | TCoerc         : Kind                                                   -> RawHaskType   (* (+>)     *)
  | TApp           : RawHaskType                  ->     RawHaskType        -> RawHaskType   (* φ φ      *)
  | TFCApp         : ∀n, TyFunConst n             -> vec RawHaskType n      -> RawHaskType   (* S_n      *)
  | TAll           : Kind  -> (TV -> RawHaskType)                           -> RawHaskType   (* ∀a:κ.φ   *)
  | TCode          : RawHaskType -> RawHaskType                             -> RawHaskType   (* from λ^α *).

  (* the "kind" of a coercion is a pair of types *)
  Inductive RawCoercionKind : Type := mkRawCoercionKind : RawHaskType -> RawHaskType -> RawCoercionKind.

  Section CV.

    (* the PHOAS type which stands for coercion variables of System FC *)
    Context {CV:Type}.

    (* Figure 7: γ, δ *)
    Inductive RawHaskCoer : Prop :=
    | CoVar          : CV                                           -> RawHaskCoer (* g      *)
    | CoType         : RawHaskType                                  -> RawHaskCoer (* τ      *)
    | CoApp          : RawHaskCoer -> RawHaskCoer                   -> RawHaskCoer (* γ γ    *)
    | CoAppT         : RawHaskCoer -> RawHaskType                   -> RawHaskCoer (* γ@v    *)
    | CoCFApp        : ∀n, CoFunConst n -> vec RawHaskCoer n        -> RawHaskCoer (* C   γⁿ *)
    | CoTFApp        : ∀n, TyFunConst n -> vec RawHaskCoer n        -> RawHaskCoer (* S_n γⁿ *)
    | CoAll          : Kind  -> (TV -> RawHaskCoer)                 -> RawHaskCoer (* ∀a:κ.γ *)
    | CoSym          : RawHaskCoer                                  -> RawHaskCoer (* sym    *)
    | CoComp         : RawHaskCoer -> RawHaskCoer                   -> RawHaskCoer (* ◯      *)
    | CoLeft         : RawHaskCoer                                  -> RawHaskCoer (* left   *)
    | CoRight        : RawHaskCoer                                  -> RawHaskCoer (* right  *).

  End CV.
End Raw.

Implicit Arguments TCon   [ [TV] [n]].
Implicit Arguments TFCApp [ [TV] [n]].
Implicit Arguments RawHaskType  [ ].
Implicit Arguments RawHaskCoer  [ ].
Implicit Arguments RawCoercionKind [ ].

Notation "t1 ---> t2"        := (fun TV env => (@TApp _ (@TApp _ (@TCon TV _ ArrowTyCon) (t1 TV env)) (t2 TV env))).
Notation "φ₁ ∼∼ φ₂ : κ ⇒ φ₃" :=
   (fun TV env => @TApp _ (@TApp _ (@TCon _ _ ArrowTyCon) (@TApp _ (@TApp _ (@TCoerc _ κ) (φ₁ TV env)) (φ₂ TV env))) (φ₃ TV env)).



(* Kind and Coercion Environments *)
(*
 *  In System FC, the environment consists of three components, each of
 *  whose well-formedness depends on all of those prior to it:
 *
 *    1. (TypeEnv)        The list of free type     variables and their kinds
 *    2. (CoercionEnv)    The list of free coercion variables and the pair of types between which it witnesses coercibility
 *    3. (Tree ??CoreVar) The list of free value    variables and the type of each one
 *)

Definition TypeEnv                                                         := list Kind.
Definition InstantiatedTypeEnv     (TV:Type)   (Γ:TypeEnv)                 := vec TV (length Γ).
Definition HaskCoercionKind                    (Γ:TypeEnv)                 := ∀ TV, InstantiatedTypeEnv TV Γ -> @RawCoercionKind TV.
Definition CoercionEnv                         (Γ:TypeEnv)                 := list (HaskCoercionKind Γ).
Definition InstantiatedCoercionEnv (TV CV:Type)(Γ:TypeEnv)(Δ:CoercionEnv Γ):= vec CV (length Δ).


(* A (HaskXX Γ) is an XX which is valid in environments of shape Γ; they are always PHOAS-uninstantiated *)
Definition HaskTyVar (Γ:TypeEnv) :=  forall TV    (env:@InstantiatedTypeEnv TV Γ), TV.
Definition HaskCoVar Γ Δ         :=  forall TV CV (env:@InstantiatedTypeEnv TV Γ)(cenv:@InstantiatedCoercionEnv TV CV Γ Δ), CV.
Definition HaskLevel (Γ:TypeEnv) :=  list (HaskTyVar Γ).
Definition HaskType         (Γ:TypeEnv)                  := ∀ TV, @InstantiatedTypeEnv TV    Γ -> RawHaskType           TV.
Definition HaskCoercion Γ Δ := ∀ TV CV,
  @InstantiatedTypeEnv TV Γ -> @InstantiatedCoercionEnv TV CV Γ Δ -> RawHaskCoer TV CV.
Inductive  LeveledHaskType (Γ:TypeEnv) := mkLeveledHaskType : HaskType Γ -> HaskLevel Γ -> LeveledHaskType Γ.
Definition FreshHaskTyVar {Γ}(κ:Kind)  : HaskTyVar (κ::Γ) := fun TV env => vec_head env.
Definition HaskTAll {Γ}(κ:Kind)(σ:forall TV (env:@InstantiatedTypeEnv TV Γ), TV -> RawHaskType TV) : HaskType Γ
  := fun TV env => TAll κ (σ TV env).
Definition HaskTApp {Γ}(σ:forall TV (env:@InstantiatedTypeEnv TV Γ), TV -> RawHaskType TV)(cv:HaskTyVar Γ) : HaskType Γ
  := fun TV env => σ TV env (cv TV env).
Definition HaskBrak {Γ}(v:HaskTyVar Γ)(t:HaskType Γ) : HaskType Γ := fun TV env => @TCode TV (TVar (v TV env)) (t TV env).
Definition HaskTCon {Γ}{n}(tc:TyCon n) : HaskType Γ := fun TV ite => TCon tc.
Definition HaskAppT {Γ}(t1 t2:HaskType Γ) : HaskType Γ := fun TV ite => TApp (t1 TV ite) (t2 TV ite).
Definition mkHaskCoercionKind {Γ}(t1 t2:HaskType Γ) : HaskCoercionKind Γ :=
 fun TV ite => mkRawCoercionKind (t1 TV ite) (t2 TV ite).


(* PHOAS substitution on types *)
Definition substT {Γ}(exp:forall TV (env:@InstantiatedTypeEnv TV Γ), TV -> RawHaskType TV)(v:@HaskType Γ) : @HaskType Γ
  := fun TV env =>
    (fix flattenT (exp: RawHaskType (RawHaskType TV)) : RawHaskType TV :=
     match exp with
    | TVar       x        => x
    | TAll       k y      => TAll      k (fun v => flattenT (y (TVar v)))
    | TApp       x y      => TApp      (flattenT x) (flattenT y)
    | TCon   n   tc       => TCon      tc
    | TCoerc     k        => TCoerc    k
    | TCode      v e      => TCode     (flattenT v) (flattenT e)
    | TFCApp     n tfc lt => TFCApp    tfc
      ((fix flatten_vec n (expv:vec (RawHaskType (RawHaskType TV)) n) : vec (RawHaskType TV) n :=
        match expv in vec _ N return vec (RawHaskType TV) N with
          | vec_nil => vec_nil
          | x:::y   => (flattenT x):::(flatten_vec _ y)
        end) n lt)
    end)
    (exp (RawHaskType TV) (vec_map (fun tv => TVar tv) env) (v TV env)).
Notation "t @@  l" := (@mkLeveledHaskType _ t l) (at level 20).
Notation "t @@@ l" := (mapOptionTree (fun t' => t' @@ l) t) (at level 20).
Notation "'<[' a '|-' t ']>'" := (@HaskBrak _ a t).




(* A "tag" is something that distinguishes one case branch from another; it's a lot like Core's AltCon *)
Inductive Tag {n:nat}(tc:TyCon n) : Type :=
| TagDefault :                                   Tag tc
| TagLiteral : forall lit:HaskLiteral ,          Tag tc (* FIXME: solution is a new StrongLiteral indexed by a tycon *)
| TagDataCon : forall m q z, DataCon tc m q z -> Tag tc.

(* the number of value variables bound in branches with the given tag *)
Definition tagNumValVars {n}{tc:TyCon n}(tag:Tag tc) : nat :=
  match tag with
    | TagDefault          => 0
    | TagLiteral  lit     => 0
    | TagDataCon m q z dc => z
  end.

(* the number of existential type variables bound in branches with the given tag *)
Definition tagNumExVars {n}{tc:TyCon n}(tag:Tag tc) : nat :=
  match tag with
    | TagDefault          => 0
    | TagLiteral  lit     => 0
    | TagDataCon m q z dc => m
  end.

(* the number of coercion variables bound in branches with the given tag *)
Definition tagNumCoVars {n}{tc:TyCon n}(tag:Tag tc) : nat :=
  match tag with
    | TagDefault          => 0
    | TagLiteral  lit     => 0
    | TagDataCon m q z dc => q
  end.

Definition caseType {Γ:TypeEnv}{n}(tc:TyCon n)(atypes:vec (HaskType Γ) n) :=
  fold_left HaskAppT (vec2list atypes) (HaskTCon(Γ:=Γ) tc).

Record StrongAltCon {n}{tc:TyCon n}{alt:Tag tc} :=
{ cb_akinds    :  vec Kind n
; cb_ekinds    :  vec Kind (tagNumExVars alt)
; cb_kinds     := app (vec2list cb_akinds) (vec2list cb_ekinds)
; cb_coercions :  vec (HaskType cb_kinds * HaskType cb_kinds) (tagNumCoVars alt)
; cb_types     :  vec (HaskType cb_kinds) (tagNumValVars alt)
}.
Implicit Arguments StrongAltCon [[n][tc]].










(* FIXME: it's a mess below this point *)


Definition unAddKindFromInstantiatedTypeEnv {Γ:TypeEnv}{κ:Kind}{TV:Type}(ite:InstantiatedTypeEnv TV (κ::Γ)) := vec_tail ite.
Definition addKindToCoercionEnv (Γ:TypeEnv)(Δ:CoercionEnv Γ)(κ:Kind) : CoercionEnv (κ::Γ) :=
  map (fun f => (fun TV ite => f TV (unAddKindFromInstantiatedTypeEnv ite))) Δ.
Definition addKindToInstantiatedTypeEnv {Γ:TypeEnv}{TV:Type}(env:InstantiatedTypeEnv TV Γ)(tv:TV)(κ:Kind)
  : InstantiatedTypeEnv TV (κ::Γ) := tv:::env.
Definition addKindToInstantiatedCoercionEnv {Γ:TypeEnv}{Δ}{TV CV:Type}(env:InstantiatedCoercionEnv TV CV Γ Δ)(tv:TV)(κ:Kind)
  : InstantiatedCoercionEnv TV CV (κ::Γ) (addKindToCoercionEnv Γ Δ κ).
    simpl.
    unfold InstantiatedCoercionEnv.
    unfold addKindToCoercionEnv.
    simpl.
    rewrite <- map_preserves_length.
    apply env.
    Defined.
Definition typeEnvContainsType {Γ}{TV:Type}(env:InstantiatedTypeEnv TV Γ)(tv:TV)(κ:Kind) : Prop
  := @vec_In _ _ (tv,κ) (vec_zip env (list2vec Γ)).
Definition coercionEnvContainsCoercion {Γ}{Δ}{TV CV:Type}(ite:InstantiatedTypeEnv TV Γ)
  (ice:InstantiatedCoercionEnv TV CV Γ Δ)(cv:CV)(ck:RawCoercionKind TV)
  := @vec_In _ _ (cv,ck) (vec_zip ice (vec_map (fun f => f TV ite) (list2vec Δ))).
Definition addCoercionToCoercionEnv {Γ}(Δ:CoercionEnv Γ)(κ:HaskCoercionKind Γ) : CoercionEnv Γ :=
  κ::Δ.
Definition addCoercionToInstantiatedCoercionEnv {Γ}{Δ}{κ}{TV CV}(ice:InstantiatedCoercionEnv TV CV Γ Δ)(cv:CV)
  : InstantiatedCoercionEnv TV CV Γ (addCoercionToCoercionEnv Δ κ).
  simpl.
  unfold addCoercionToCoercionEnv; simpl.
  unfold InstantiatedCoercionEnv; simpl. 
  apply vec_cons; auto.
  Defined.
Notation "env  ∋  tv : κ"        := (@typeEnvContainsType  _ _ env tv κ).
Notation "env '+' tv : κ"        := (@addKindToInstantiatedTypeEnv  _ _ env tv κ).

(* the various "weak" functions turn a HaskXX-in-Γ into a HaskXX-in-(κ::Γ) *)
Definition weakITE  {Γ:TypeEnv}{κ}{TV}(ite:InstantiatedTypeEnv TV (κ::Γ)) : InstantiatedTypeEnv TV Γ := vec_tail ite.
Definition weakITE' {Γ:TypeEnv}{κ}{TV}(ite:InstantiatedTypeEnv TV (app κ Γ)) : InstantiatedTypeEnv TV Γ.
  induction κ; auto. apply IHκ. inversion ite; subst. apply X0. Defined.
Definition weakCE   {Γ:TypeEnv}{κ}(Δ:CoercionEnv Γ) : CoercionEnv (κ::Γ) := map (fun x => (fun tv ite => x tv (weakITE ite))) Δ.
Definition weakV  {Γ:TypeEnv}{κ}(cv':HaskTyVar Γ) : HaskTyVar (κ::Γ) := fun TV ite => (cv' TV (weakITE ite)).
Definition weakV' {Γ:TypeEnv}{κ}(cv':HaskTyVar Γ) : HaskTyVar (app κ Γ).
  induction κ; auto. apply weakV; auto. Defined.
Definition weakT {Γ:TypeEnv}{κ:Kind}(lt:HaskType Γ) : HaskType (κ::Γ) := fun TV ite => lt TV (weakITE ite).
Definition weakL  {Γ}{κ}(lt:HaskLevel Γ) : HaskLevel (κ::Γ) := map weakV lt.
Definition weakT' {Γ}{κ}(lt:HaskType Γ) : HaskType (app κ Γ).
  induction κ; auto. apply weakT; auto. Defined.
Definition weakT'' {Γ}{κ}(lt:HaskType Γ) : HaskType (app Γ κ).
unfold HaskType in *.
unfold InstantiatedTypeEnv in *.
intros.
apply vec_chop in X.
apply lt.
apply X.
Defined.
Definition lamer {a}{b}{c}(lt:HaskType (app (app a  b) c)) : HaskType  (app a (app b c)).
rewrite <- ass_app in lt.
exact lt.
Defined.
Definition weakL' {Γ}{κ}(lev:HaskLevel Γ) : HaskLevel (app κ Γ).
  induction κ; auto. apply weakL; auto. Defined.
Definition weakLT {Γ}{κ}(lt:LeveledHaskType Γ) : LeveledHaskType (κ::Γ) := match lt with t @@ l => weakT t @@ weakL l end.
Definition weakLT' {Γ}{κ}(lt:LeveledHaskType Γ) : LeveledHaskType (app κ Γ)
  := match lt with t @@ l => weakT' t @@ weakL' l end.
Definition weakCE' {Γ:TypeEnv}{κ}(Δ:CoercionEnv Γ) : CoercionEnv (app κ Γ).
  induction κ; auto. apply weakCE; auto. Defined.
Definition weakICE  {Γ:TypeEnv}{κ}{Δ:CoercionEnv Γ}{TV}{CV}(ice:InstantiatedCoercionEnv TV CV (κ::Γ) (weakCE Δ))
  : InstantiatedCoercionEnv TV CV Γ Δ.
  intros.
  unfold InstantiatedCoercionEnv; intros.
  unfold InstantiatedCoercionEnv in ice.
  unfold weakCE in ice.
  simpl in ice.
  rewrite <- map_preserves_length in ice.
  apply ice.
  Defined.
Definition weakICE' {Γ:TypeEnv}{κ}{Δ:CoercionEnv Γ}{TV}{CV}(ice:InstantiatedCoercionEnv TV CV (app κ Γ) (weakCE' Δ))
  : InstantiatedCoercionEnv TV CV Γ Δ.
  induction κ; auto. apply IHκ. eapply weakICE. apply ice. Defined.
Definition weakCV {Γ}{Δ}{κ}(cv':HaskCoVar Γ Δ) : HaskCoVar (κ::Γ) (weakCE Δ) :=
  fun TV CV ite ice => (cv' TV CV (weakITE ite) (weakICE ice)).
Definition weakC  {Γ}{κ}{Δ}(c:HaskCoercion Γ Δ) : HaskCoercion (κ::Γ) (weakCE Δ) :=
  fun TV CV ite ice => c TV CV (weakITE ite) (weakICE ice).
Definition weakF {Γ:TypeEnv}{κ:Kind}(f:forall TV (env:@InstantiatedTypeEnv TV Γ), TV -> RawHaskType TV) : 
  forall TV (env:@InstantiatedTypeEnv TV (κ::Γ)), TV -> RawHaskType TV
  := fun TV ite tv => (f TV (weakITE ite) tv).

(***************************************************************************************************)
(* Well-Formedness of Types and Coercions                                                          *)
(* also represents production "S_n:κ" of Γ because these can only wind up in Γ via rule (Type) *)
Inductive TypeFunctionDecl (n:nat)(tfc:TyFunConst n)(vk:vec Kind n) : Type :=
  mkTFD : Kind -> TypeFunctionDecl n tfc vk.


(* Figure 8, upper half *)
Inductive WellKinded_RawHaskType (TV:Type)
  : forall Γ:TypeEnv, InstantiatedTypeEnv TV Γ -> RawHaskType TV -> Kind -> Prop :=
  | WFTyVar  : forall Γ env κ d,
                env∋d:κ ->
                WellKinded_RawHaskType TV Γ env (TVar d) κ
  | WFTyApp  : forall Γ env κ₁ κ₂ σ₁ σ₂,
                WellKinded_RawHaskType TV Γ env σ₁  (κ₁ ⇛ κ₂)  ->
                WellKinded_RawHaskType TV Γ env σ₂        κ₂   ->
                WellKinded_RawHaskType TV Γ env (TApp σ₁ σ₂) κ₂
  | WFTyAll  : forall Γ (env:InstantiatedTypeEnv TV Γ) κ     σ    ,
                (∀ a, WellKinded_RawHaskType TV _ (@addKindToInstantiatedTypeEnv _ TV env a κ) (σ a) ★ )        -> 
                WellKinded_RawHaskType TV _  env      (TAll κ σ) ★ 
  | TySCon   : forall Γ env n tfc lt vk ι ,
                @TypeFunctionDecl n tfc vk  ->
                ListWellKinded_RawHaskType TV Γ _ env lt vk ->
                WellKinded_RawHaskType TV Γ env (TFCApp tfc lt) ι
with ListWellKinded_RawHaskType (TV:Type)
  : forall (Γ:TypeEnv) n, InstantiatedTypeEnv TV Γ -> vec (RawHaskType TV) n -> vec Kind n -> Prop :=
  | ListWFRawHaskTypenil  : forall Γ env,
                ListWellKinded_RawHaskType TV Γ 0 env  vec_nil vec_nil
  | ListWFRawHaskTypecons : forall Γ env n t k lt lk,
                WellKinded_RawHaskType     TV Γ env      t       k  ->
                ListWellKinded_RawHaskType TV Γ n env     lt      lk  ->
                ListWellKinded_RawHaskType TV Γ (S n) env  (t:::lt) (k:::lk).

(*
Fixpoint kindOfRawHaskType {TV}(rht:RawHaskType Kind) : Kind :=
match rht with
  | TVar   k    => k
  | TCon   n tc => ̱★ (* FIXME: use the StrongAltCon *)
  | TCoerc k    => k ⇛ (k ⇛ (★ ⇛ ★ ))
  | TApp   ht1 ht2        : RawHaskType                  ->     RawHaskType        -> RawHaskType   (* φ φ      *)
  | TFCApp         : ∀n, TyFunConst n             -> vec RawHaskType n      -> RawHaskType   (* S_n      *)
  | TAll           : Kind  -> (TV -> RawHaskType)                           -> RawHaskType   (* ∀a:κ.φ   *)
  | TCode          : RawHaskType -> RawHaskType                             -> RawHaskType   (* from λ^α *).
*)
Definition WellKindedHaskType Γ (ht:HaskType Γ) κ :=
  forall TV env, WellKinded_RawHaskType TV Γ env (ht TV env) κ.
  Notation "Γ '⊢ᴛy' σ : κ" := (WellKindedHaskType Γ σ κ).



(* "decl", production for "axiom" *)
Structure AxiomDecl (n:nat)(ccon:CoFunConst n)(vk:vec Kind n){TV:Type} : Type :=
{ axd_τ : vec TV n -> RawHaskType TV
; axd_σ : vec TV n -> RawHaskType TV
}.




Section WFCo.
  Context {TV:Type}.
  Context {CV:Type}.

  (* local notations *)
  Notation "ienv '⊢ᴛy' σ : κ"              := (@WellKinded_RawHaskType TV _ ienv σ κ).
  Notation "env  ∋  cv : t1 ∼ t2 : Γ : t"  := (@coercionEnvContainsCoercion Γ _ TV CV t env cv (@mkRawCoercionKind _ t1 t2))
                 (at level 20, t1 at level 99, t2 at level 99, t at level 99).
  Reserved Notation "ice '⊢ᴄᴏ' γ : a '∼' b : Δ : Γ : ite"
        (at level 20, γ at level 99, b at level 99, Δ at level 99, ite at level 99, Γ at level 99).

  (* Figure 8, lower half *)
  Inductive WFCoercion:forall Γ (Δ:CoercionEnv Γ),
    @InstantiatedTypeEnv TV Γ ->
    @InstantiatedCoercionEnv TV CV Γ Δ ->
    @RawHaskCoer TV CV -> @RawCoercionKind TV -> Prop :=.
(*
  | CoTVar':∀ Γ Δ t e c σ τ,
    (@coercionEnvContainsCoercion Γ _ TV CV t e c (@mkRawCoercionKind _ σ τ)) -> e⊢ᴄᴏ CoVar c : σ ∼ τ  : Δ : Γ : t
  | CoRefl :∀ Γ Δ t e   τ κ,                                         t ⊢ᴛy τ :κ    -> e⊢ᴄᴏ CoType τ    :         τ ∼ τ  : Δ :Γ: t
  | Sym    :∀ Γ Δ t e γ σ τ,                            (e⊢ᴄᴏ γ : σ ∼ τ : Δ : Γ:t)  -> e⊢ᴄᴏ CoSym  γ    :         τ ∼ σ  : Δ :Γ: t
  | Trans  :∀ Γ Δ t e γ₁ γ₂ σ₁ σ₂ σ₃,(e⊢ᴄᴏ γ₁:σ₁∼σ₂:Δ:Γ:t) -> (e⊢ᴄᴏ γ₂:σ₂∼σ₃:Δ:Γ:t) -> e⊢ᴄᴏ CoComp γ₁ γ₂:        σ₁ ∼ σ₃ : Δ :Γ: t
  | Left   :∀ Γ Δ t e γ σ₁ σ₂ τ₁ τ₂,(e⊢ᴄᴏ γ : TApp σ₁ σ₂ ∼ TApp τ₁ τ₂ :Δ:Γ:t    )  -> e⊢ᴄᴏ CoLeft  γ   :        σ₁ ∼ τ₁ : Δ :Γ: t
  | Right  :∀ Γ Δ t e γ σ₁ σ₂ τ₁ τ₂,(e⊢ᴄᴏ γ : TApp σ₁ σ₂ ∼ TApp τ₁ τ₂ :Δ:Γ:t   )   -> e⊢ᴄᴏ CoRight γ   :        σ₂ ∼ τ₂ : Δ :Γ: t
  | SComp  :∀ Γ Δ t e γ n S σ τ κ,
            ListWFCo Γ Δ t e γ σ τ -> t ⊢ᴛy TFCApp(n:=n) S σ : κ  -> e⊢ᴄᴏ CoTFApp S γ : TFCApp S σ∼TFCApp S τ : Δ : Γ : t
  | CoAx   :∀ Γ Δ t e n C κ γ, forall (σ₁:vec TV n) (σ₂:vec TV n), forall (ax:@AxiomDecl n C κ TV),
    ListWFCo                              Γ Δ t e γ (map TVar (vec2list σ₁)) (map TVar (vec2list σ₂)) ->
    ListWellKinded_RawHaskType TV Γ t   (map TVar (vec2list σ₁))            (vec2list κ)  ->
    ListWellKinded_RawHaskType TV Γ t   (map TVar (vec2list σ₂))            (vec2list κ)  ->
    e⊢ᴄᴏ CoCFApp C γ : axd_σ _ _ _ ax σ₁ ∼ axd_τ _ _ _ ax σ₂ : Δ : Γ : t

  | WFCoAll  : forall Γ Δ κ (t:InstantiatedTypeEnv TV Γ) (e:InstantiatedCoercionEnv TV CV (κ::Γ) (weakCE Δ)) γ σ τ    ,
      (∀ a,           e ⊢ᴄᴏ (        γ a) : (       σ a) ∼ (       τ a) : _ : _ : (t + a : κ))
      ->    weakICE e ⊢ᴄᴏ (CoAll κ γ  ) : (TAll κ σ  ) ∼ (TAll κ τ  ) : Δ : Γ :  t

  | Comp   :forall Γ Δ t e γ₁ γ₂ σ₁ σ₂ τ₁ τ₂ κ,
            (t ⊢ᴛy TApp σ₁ σ₂:κ)->
            (e⊢ᴄᴏ γ₁:σ₁∼τ₁:Δ:Γ:t)->
            (e⊢ᴄᴏ γ₂:σ₂∼τ₂:Δ:Γ:t) ->
            e⊢ᴄᴏ (CoApp γ₁ γ₂) : (TApp σ₁ σ₂) ∼ (TApp τ₁ τ₂) : Δ:Γ:t

  | CoInst :forall Γ Δ t e σ τ κ γ (v:∀ TV, InstantiatedTypeEnv TV Γ -> RawHaskType TV),
          t ⊢ᴛy v TV t : κ  ->
            (e⊢ᴄᴏ γ:HaskTAll κ σ _ t ∼ HaskTAll κ τ _ t:Δ:Γ:t) ->
            e⊢ᴄᴏ CoAppT γ (v TV t) : substT σ v TV t ∼substT τ v TV t : Δ : Γ : t
  with ListWFCo  : forall Γ (Δ:CoercionEnv Γ),
     @InstantiatedTypeEnv TV Γ ->
     InstantiatedCoercionEnv TV CV Γ Δ ->
     list (RawHaskCoer TV CV) -> list (RawHaskType TV) -> list (RawHaskType TV) -> Prop :=
  | LWFCo_nil  : ∀ Γ Δ t e ,                                                            ListWFCo Γ Δ t e nil     nil     nil
  | LWFCo_cons : ∀ Γ Δ t e a b c la lb lc, (e⊢ᴄᴏ a : b∼c : Δ : Γ : t )->
    ListWFCo Γ Δ t e la lb lc -> ListWFCo Γ Δ t e (a::la) (b::lb) (c::lc)
  where "ice '⊢ᴄᴏ' γ : a '∼' b : Δ : Γ : ite" := (@WFCoercion Γ Δ ite ice γ (@mkRawCoercionKind _ a b)).
*)
End WFCo.

Definition WFCCo (Γ:TypeEnv)(Δ:CoercionEnv Γ)(γ:HaskCoercion Γ Δ)(a b:HaskType Γ) :=
  forall {TV CV:Type}(env:@InstantiatedTypeEnv TV Γ)(cenv:InstantiatedCoercionEnv TV CV Γ Δ),
    @WFCoercion _ _ Γ Δ env cenv (γ TV CV env cenv) (@mkRawCoercionKind _ (a TV env) (b TV env)).
    Notation "Δ '⊢ᴄᴏ' γ : a '∼' b" := (@WFCCo _ Δ γ a b).

  Definition literalType (lit:HaskLiteral){Γ} : HaskType Γ := fun TV ite => (TCon (haskLiteralToTyCon lit)).
  Notation "a ∼∼∼ b" := (mkHaskCoercionKind a b) (at level 18).


Fixpoint update_ξ
  `{EQD_VV:EqDecidable VV}{Γ}(ξ:VV -> LeveledHaskType Γ)(vt:list (VV * LeveledHaskType Γ)) : VV -> LeveledHaskType Γ :=
  match vt with
    | nil => ξ
    | (v,τ)::tl => fun v' => if eqd_dec v v' then τ else (update_ξ ξ tl) v'
  end.











(*
Definition literalType (lit:Literal) : ∀ Γ, HaskType Γ := fun Γ TV ite => (TCon (literalTyCon lit)).
Definition unlev {Γ:TypeEnv}(lht:LeveledHaskType Γ) : HaskType Γ   := match lht with t @@ l => t end.
Definition getlev {Γ:TypeEnv}(lht:LeveledHaskType Γ) : HaskLevel Γ := match lht with t @@ l => l end.
(* the type of the scrutinee in a case branch *)
Require Import Coq.Arith.EqNat.
Definition bump (n:nat) : {z:nat & lt z n} -> {z:nat & lt z (S n)}.
  intros.
  destruct H.
  exists x; omega.
  Defined.
Definition vecOfNats (n:nat) : vec {z:nat & lt z n} n.
  induction n.
  apply vec_nil.
  apply vec_cons.
    exists n; omega.
    apply (vec_map (bump _)); auto.
    Defined.
Definition var_eq_dec {Γ:TypeEnv}(hv1 hv2:HaskTyVar Γ) : sumbool (eq hv1 hv2) (not (eq hv1 hv2)).
  set (hv1 _ (vecOfNats _)) as hv1'.
  set (hv2 _ (vecOfNats _)) as hv2'.
  destruct hv1' as [hv1_n hv1_pf].
  destruct hv2' as [hv2_n hv2_pf].
  clear hv1_pf.
  clear hv2_pf.
  set (eq_nat_decide hv1_n hv2_n) as dec.
  destruct dec.
    left.  admit.
    right. intro. apply n. assert (hv1_n=hv2_n). admit. rewrite H0. apply eq_nat_refl.
  Defined.
(* equality on levels is decidable *)
Definition lev_eq_dec {Γ:TypeEnv}(l1 l2:HaskLevel Γ) : sumbool (eq l1 l2) (not (eq l1 l2))
  := @list_eq_dec (HaskTyVar Γ) (@var_eq_dec Γ) l1 l2.
*)





(* just like GHC's AltCon, but using PHOAS types and coercions *)
Record StrongAltConInContext {n}{tc:TyCon n}{Γ}{atypes:vec (HaskType Γ) n} :=
{ cbi_tag       :  Tag tc
; cbi_cb        :  StrongAltCon cbi_tag
; cbi_Γ         :  TypeEnv := app (vec2list (cb_ekinds cbi_cb)) Γ
; cbi_Δ         :  CoercionEnv cbi_Γ
; cbi_types     :  vec (LeveledHaskType (app (vec2list (cb_ekinds cbi_cb)) Γ)) (tagNumValVars cbi_tag)
}.
Implicit Arguments StrongAltConInContext [[n][Γ]].

