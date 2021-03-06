(*********************************************************************************************************************************)
(* PCF:                                                                                                          *)
(*                                                                                                                               *)
(*    An alternate representation for HaskProof which ensures that deductions on a given level are grouped into contiguous       *)
(*    blocks.  This representation lacks the attractive compositionality properties of HaskProof, but makes it easier to         *)
(*    perform the flattening process.                                                                                            *)
(*                                                                                                                               *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import NaturalDeduction.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Algebras_ch4.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.
Require Import ProductCategories_ch1_6_1.
Require Import OppositeCategories_ch1_6_2.
Require Import Enrichment_ch2_8.
Require Import Subcategories_ch7_1.
Require Import NaturalTransformations_ch7_4.
Require Import NaturalIsomorphisms_ch7_5.
Require Import MonoidalCategories_ch7_8.
Require Import Coherence_ch7_8.

Require Import HaskKinds.
Require Import HaskCoreTypes.
Require Import HaskLiterals.
Require Import HaskTyCons.
Require Import HaskStrongTypes.
Require Import HaskProof.
Require Import NaturalDeduction.
Require Import NaturalDeductionCategory.

Require Import HaskStrongTypes.
Require Import HaskStrong.
Require Import HaskProof.
Require Import HaskStrongToProof.
Require Import HaskProofToStrong.
Require Import ProgrammingLanguage.

Open Scope nd_scope.


(*
 *  The flattening transformation.  Currently only TWO-level languages are
 *  supported, and the level-1 sublanguage is rather limited.
*
 *  This file abuses terminology pretty badly.  For purposes of this file,
 *  "PCF" means "the level-1 sublanguage" and "FC" (aka System FC) means 
 *  the whole language (level-0 language including bracketed level-1 terms)
 *)
Section PCF.

  Section PCF.

  Context {ndr_systemfc:@ND_Relation _ Rule}.
  Context Γ (Δ:CoercionEnv Γ).

  Definition PCFJudg (ec:HaskTyVar Γ ECKind) :=
    @prod (Tree ??(HaskType Γ ★)) (Tree ??(HaskType Γ ★)).
  Definition pcfjudg (ec:HaskTyVar Γ ECKind) :=
    @pair (Tree ??(HaskType Γ ★)) (Tree ??(HaskType Γ ★)).

  (* given an PCFJudg at depth (ec::depth) we can turn it into an PCFJudg
   * from depth (depth) by wrapping brackets around everything in the
   * succedent and repopulating *)
  Definition brakify {ec} (j:PCFJudg ec) : Judg :=
    match j with
      (Σ,τ) => Γ > Δ > (Σ@@@(ec::nil)) |- (mapOptionTree (fun t => HaskBrak ec t) τ @@@ nil)
      end.

  Definition pcf_vars {Γ}(ec:HaskTyVar Γ ECKind)(t:Tree ??(LeveledHaskType Γ ★)) : Tree ??(HaskType Γ ★)
    := mapOptionTreeAndFlatten (fun lt =>
      match lt with t @@ l => match l with
                                | ec'::nil => if eqd_dec ec ec' then [t] else []
                                | _ => []
                              end
      end) t.

  Inductive MatchingJudgments {ec} : Tree ??(PCFJudg ec) -> Tree ??Judg -> Type :=
    | match_nil    : MatchingJudgments [] []
    | match_branch : forall a b c d, MatchingJudgments a b -> MatchingJudgments c d -> MatchingJudgments (a,,c) (b,,d)
    | match_leaf   : 
      forall Σ τ lev,
        MatchingJudgments
          [((pcf_vars ec Σ)         ,                              τ        )]
          [Γ > Δ >              Σ  |- (mapOptionTree (HaskBrak ec) τ @@@ lev)].

  Definition pcfjudg2judg ec (cj:PCFJudg ec) :=
    match cj with (Σ,τ) => Γ > Δ > (Σ @@@ (ec::nil)) |- (τ @@@ (ec::nil)) end.

  (* Rules allowed in PCF; i.e. rules we know how to turn into GArrows     *)
  (* Rule_PCF consists of the rules allowed in flat PCF: everything except *)
  (* AppT, AbsT, AppC, AbsC, Cast, Global, and some Case statements        *)
  Inductive Rule_PCF (ec:HaskTyVar Γ ECKind)
    : forall (h c:Tree ??(PCFJudg ec)), Rule (mapOptionTree (pcfjudg2judg ec) h) (mapOptionTree (pcfjudg2judg ec) c) -> Type :=
  | PCF_RArrange    : ∀ x y t     a,  Rule_PCF ec [(_, _)] [(_, _)] (RArrange Γ Δ (x@@@(ec::nil)) (y@@@(ec::nil)) (t@@@(ec::nil)) a)
  | PCF_RLit        : ∀ lit        ,  Rule_PCF ec [           ] [ ([],[_]) ] (RLit   Γ Δ  lit (ec::nil))
  | PCF_RNote       : ∀ Σ τ   n    ,  Rule_PCF ec [(_,[_])] [(_,[_])] (RNote  Γ Δ  (Σ@@@(ec::nil)) τ         (ec::nil) n)
  | PCF_RVar        : ∀ σ          ,  Rule_PCF ec [           ] [([_],[_])] (RVar   Γ Δ    σ         (ec::nil)  )
  | PCF_RLam        : ∀ Σ tx te    ,  Rule_PCF ec [((_,,[_]),[_])] [(_,[_])] (RLam   Γ Δ  (Σ@@@(ec::nil)) tx te  (ec::nil)  )

  | PCF_RApp             : ∀ Σ Σ' tx te ,
    Rule_PCF ec ([(_,[_])],,[(_,[_])]) [((_,,_),[_])]
    (RApp Γ Δ (Σ@@@(ec::nil))(Σ'@@@(ec::nil)) tx te (ec::nil))

  | PCF_RLet             : ∀ Σ Σ' σ₂   p,
    Rule_PCF ec ([(_,[_])],,[((_,,[_]),[_])]) [((_,,_),[_])]
    (RLet Γ Δ (Σ@@@(ec::nil)) (Σ'@@@(ec::nil)) σ₂ p (ec::nil))

  | PCF_RVoid      :                 Rule_PCF ec [           ] [([],[])] (RVoid   Γ Δ  )
(*| PCF_RLetRec          : ∀ Σ₁ τ₁ τ₂   ,  Rule_PCF (ec::nil) _ _ (RLetRec Γ Δ Σ₁ τ₁ τ₂ (ec::nil) )*)
  | PCF_RJoin    : ∀ Σ₁ Σ₂ τ₁ τ₂,  Rule_PCF ec ([(_,_)],,[(_,_)]) [((_,,_),(_,,_))]
    (RJoin Γ Δ (Σ₁@@@(ec::nil)) (Σ₂@@@(ec::nil)) (τ₁@@@(ec::nil)) (τ₂@@@(ec::nil))).
  (* need int/boolean case *)
  Implicit Arguments Rule_PCF [ ].

  Definition PCFRule lev h c := { r:_ & @Rule_PCF lev h c r }.
  End PCF.

  Definition mkEsc Γ Δ ec (h:Tree ??(PCFJudg Γ ec))
    : ND Rule
    (mapOptionTree (brakify Γ Δ) h)
    (mapOptionTree (pcfjudg2judg Γ Δ ec) h).
    apply nd_replicate; intros.
    destruct o; simpl in *.
    induction t0.
    destruct a; simpl.
    apply nd_rule.
    apply REsc.
    apply nd_id.
    apply (Prelude_error "mkEsc got multi-leaf succedent").
    Defined.

  Definition mkBrak Γ Δ ec (h:Tree ??(PCFJudg Γ ec))
    : ND Rule
    (mapOptionTree (pcfjudg2judg Γ Δ ec) h)
    (mapOptionTree (brakify Γ Δ) h).
    apply nd_replicate; intros.
    destruct o; simpl in *.
    induction t0.
    destruct a; simpl.
    apply nd_rule.
    apply RBrak.
    apply nd_id.
    apply (Prelude_error "mkBrak got multi-leaf succedent").
    Defined.

  Definition pcfToND Γ Δ : forall ec h c,
    ND (PCFRule Γ Δ ec) h c -> ND Rule (mapOptionTree (pcfjudg2judg Γ Δ ec) h) (mapOptionTree (pcfjudg2judg Γ Δ ec) c).
    intros.
    eapply (fun q => nd_map' _ q X).
    intros.
    destruct X0.
    apply nd_rule.
    apply x.
    Defined.
    
  Instance OrgPCF Γ Δ lev : @ND_Relation _ (PCFRule Γ Δ lev) :=
    { ndr_eqv := fun a b f g => (pcfToND  _ _ _ _ _ f) === (pcfToND _ _ _ _ _ g) }.
    Admitted.

  Hint Constructors Rule_Flat.

  Definition PCF_Arrange {Γ}{Δ}{lev} : forall x y z, Arrange x y -> ND (PCFRule Γ Δ lev) [(x,z)] [(y,z)].
    admit.
    Defined.

  Definition PCF_cut Γ Δ lev : forall a b c, ND (PCFRule Γ Δ lev) ([(a,b)],,[(b,c)]) [(a,c)].
    intros.
    destruct b.
    destruct o.
    destruct c.
    destruct o.

    (* when the cut is a single leaf and the RHS is a single leaf: *)
    eapply nd_comp.
      eapply nd_prod.
      apply nd_id.
      apply (PCF_Arrange [h] ([],,[h]) [h0]).
      apply AuCanL.
      eapply nd_comp; [ idtac | apply (PCF_Arrange ([],,a) a [h0]); apply ACanL ].
      apply nd_rule.
      (*
      set (@RLet Γ Δ [] (a@@@(ec::nil)) h0 h (ec::nil)) as q.
      exists q.
      apply (PCF_RLet _ [] a h0 h).
    apply (Prelude_error "cut rule invoked with [a|=[b]] [[b]|=[]]").
    apply (Prelude_error "cut rule invoked with [a|=[b]] [[b]|=[x,,y]]").
    apply (Prelude_error "cut rule invoked with [a|=[]]  [[]|=c]").
    apply (Prelude_error "cut rule invoked with [a|=[b,,c]] [[b,,c]|=z]").
    *)
    Admitted.

  Instance PCF_sequents Γ Δ lev ec : @SequentND _ (PCFRule Γ Δ lev) _ (pcfjudg Γ ec) :=
    { snd_cut := PCF_cut Γ Δ lev }.
    apply Build_SequentND.
    intros.
    induction a.
    destruct a; simpl.
    apply nd_rule.
      exists (RVar _ _ _ _).
      apply PCF_RVar.
    apply nd_rule.
      exists (RVoid _ _ ).
      apply PCF_RVoid.
    eapply nd_comp.
      eapply nd_comp; [ apply nd_llecnac | idtac ].
      apply (nd_prod IHa1 IHa2).
      apply nd_rule.
        exists (RJoin _ _ _ _ _ _). 
        apply PCF_RJoin.
      admit.
        Defined.

  Definition PCF_left Γ Δ lev a b c : ND (PCFRule Γ Δ lev) [(b,c)] [((a,,b),(a,,c))].
    eapply nd_comp; [ apply nd_llecnac | eapply nd_comp; [ idtac | idtac ] ].
    eapply nd_prod; [ apply snd_initial | apply nd_id ].
    apply nd_rule.
    set (@PCF_RJoin Γ Δ lev a b a c) as q'.
    refine (existT _ _ _).
    apply q'.
    Admitted.

  Definition PCF_right Γ Δ lev a b c : ND (PCFRule Γ Δ lev) [(b,c)] [((b,,a),(c,,a))].
    eapply nd_comp; [ apply nd_rlecnac | eapply nd_comp; [ idtac | idtac ] ].
    eapply nd_prod; [ apply nd_id | apply snd_initial ].
    apply nd_rule.
    set (@PCF_RJoin Γ Δ lev b a c a) as q'.
    refine (existT _ _ _).
    apply q'.
    Admitted.

  Instance PCF_sequent_join Γ Δ lev : @ContextND _ (PCFRule Γ Δ lev) _ (pcfjudg Γ lev) _ :=
  { cnd_expand_left  := fun a b c => PCF_left  Γ Δ lev c a b
  ; cnd_expand_right := fun a b c => PCF_right Γ Δ lev c a b }.

    intros; apply nd_rule. unfold PCFRule. simpl.
      exists (RArrange _ _ _ _ _ (AuAssoc _ _ _)).
      apply (PCF_RArrange _ _ lev ((a,,b),,c) (a,,(b,,c)) x).

    intros; apply nd_rule. unfold PCFRule. simpl.
      exists (RArrange _ _ _ _ _ (AAssoc _ _ _)).
      apply (PCF_RArrange _ _ lev (a,,(b,,c)) ((a,,b),,c) x).

    intros; apply nd_rule. unfold PCFRule. simpl.
      exists (RArrange _ _ _ _ _ (ACanL _)).
      apply (PCF_RArrange _ _ lev ([],,a) _ _).

    intros; apply nd_rule. unfold PCFRule. simpl.
      exists (RArrange _ _ _ _ _ (ACanR _)).
      apply (PCF_RArrange _ _ lev (a,,[]) _ _).

    intros; apply nd_rule. unfold PCFRule. simpl.
      exists (RArrange _ _ _ _ _ (AuCanL _)).
      apply (PCF_RArrange _ _ lev _ ([],,a) _).

    intros; apply nd_rule. unfold PCFRule. simpl.
      exists (RArrange _ _ _ _ _ (AuCanR _)).
      apply (PCF_RArrange _ _ lev _ (a,,[]) _).
      Defined.

  Instance OrgPCF_SequentND_Relation Γ Δ lev : SequentND_Relation (PCF_sequent_join Γ Δ lev) (OrgPCF Γ Δ lev).
    admit.
    Defined.

  Definition OrgPCF_ContextND_Relation Γ Δ lev
    : @ContextND_Relation _ _ _ _ _ (PCF_sequent_join Γ Δ lev) (OrgPCF Γ Δ lev) (OrgPCF_SequentND_Relation Γ Δ lev).
    admit.
    Defined.

  (* 5.1.3 *)
  Instance PCF Γ Δ lev : ProgrammingLanguage :=
  { pl_cnd     := PCF_sequent_join Γ Δ lev
  ; pl_eqv     := OrgPCF_ContextND_Relation Γ Δ lev
  }.

End PCF.
