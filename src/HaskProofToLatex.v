(*********************************************************************************************************************************)
(* HaskProofToLatex: render HaskProof's as LaTeX code using trfrac.sty                                                           *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import NaturalDeduction.
Require Import NaturalDeductionToLatex.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import HaskGeneral.
Require Import HaskLiterals.
Require Import HaskStrongTypes.
Require Import HaskStrong.
Require Import HaskProof.

(* escapifies any characters which might cause trouble for LaTeX *)
Variable sanitizeForLatex    : string      -> string.        Extract Inlined Constant sanitizeForLatex      => "sanitizeForLatex".
Variable nat2string          : nat         -> string.        Extract Inlined Constant nat2string            => "nat2string".

Open Scope string_scope.
Section ToLatex.

  Fixpoint kind2latex (k:Kind) : string :=
    match k with
    | KindType                     => "\star"
    | KindTypeFunction KindType k2 => "\star\Rightarrow "+++kind2latex k2
    | KindTypeFunction k1 k2       => "("+++kind2latex k1+++")\Rightarrow "+++kind2latex k2
    | KindUnliftedType             => "\text{\tt{\#}}"
    | KindUnboxedTuple             => "\text{\tt{(\#)}}"
    | KindArgType                  => "\text{\tt{?}}"
    | KindOpenType                 => "\text{\tt{?}}"
    end.

  Open Scope nat_scope.
  Definition var2string (n:nat) :=
    match n with
      | 0 => "x"
      | 1 => "y"
      | 2 => "z"
      | 3 => "a"
      | 4 => "b"
      | 5 => "c"
      | 6 => "d"
      | 7 => "e"
      | 8 => "f"
      | 9 => "g"
      | 10 => "h"
      | S (S (S (S (S (S (S (S (S (S (S x)))))))))) => "z_{"+++(nat2string x)+++"}"
    end.
  Close Scope nat_scope.

  Definition tyvar2greek (n:nat) :=
    match n with
      | O => "\alpha"
      | S O => "\beta"
      | S (S O) => "\xi"
      | S (S (S n)) => "\alpha_{"+++nat2string n+++"}"
    end.

  Definition covar2greek (n:nat) :=
    "{\gamma_{"+++(nat2string n)+++"}}".

  Fixpoint count (n:nat) : vec nat n :=
  match n with
    | O    => vec_nil
    | S n' => n':::(count n')
  end.

  Fixpoint type2latex (needparens:bool)(n:nat)(t:RawHaskType nat) {struct t} : string :=
    match t with
    | TVar   v                                => tyvar2greek v
    | TCon _  tc                              => "\text{\tt{"+++sanitizeForLatex (tyConToString _ tc) +++"}}"
    | TCoerc κ                                => "{\text{\tt{(+>)}}}_{"+++ kind2latex κ +++"}"
    | TApp   t1 t2                            =>
      match (match t1 with
        | TApp (TCon 2 tc) t1' => 
          if (tyCon_eq tc ArrowTyCon)
            then inl _ (if needparens
                            then "("+++(type2latex true n t1')+++"{\rightarrow}"+++(type2latex true n t2)+++")"
                            else (type2latex true n t1')+++"{\rightarrow}"+++(type2latex true n t2))
            else inr _ tt
        | _ => inr _ tt
      end) with
      | inl  x    => x
      | _         => if needparens
                     then "("+++(type2latex true n t1)+++" "+++(type2latex false n t2)+++")"
                     else (type2latex true n t1)+++" "+++(type2latex false n t2)
      end
    | TFCApp n tfc lt                         => "{\text{\tt{"+++sanitizeForLatex (tyFunToString _ tfc) +++"}}}"+++
                                                 "_{"+++(nat2string n)+++"}"+++
                                                 fold_left (fun x y => " \  "+++x+++y)
                                                 ((fix type2latex_vec (needparens:bool)(n:nat){m}(lt:vec (RawHaskType nat) m)
                                                   : list string :=
                                                   match lt with
                                                     | vec_nil => nil
                                                     | a:::b   => (type2latex needparens n a)::(type2latex_vec needparens n _ b)
                                                   end )
                                                   false n _ lt) ""
    | TAll   k f                              => let alpha := tyvar2greek n
                                                 in "(\forall "+++ alpha +++ "{:}"+++ kind2latex k +++")"+++
                                                      type2latex false (S n) (f n)
    | TCode  ec t                             => "\code{"+++(type2latex true n ec)+++"}{"+++(type2latex false n t)+++"}"
    end.

  Definition ltype2latex {Γ:TypeEnv}(t:RawHaskType nat)(lev:list nat) : string :=
    match lev with
      | nil => type2latex false O t
      | lv  => "{"+++type2latex true O t+++"}^{"+++(fold_left (fun x y => x+++":"+++y) (map tyvar2greek lv) "")+++"}"
    end.

  Fixpoint enumerate' (n:nat){T:Type}(l:list T) : list (nat * T) :=
    match l with
      | nil    => nil
      | (a::b) => (n,a)::(enumerate' (S n) b)
    end.

  Definition enumerate {T:Type}(l:list T) := enumerate' O l.

  Definition InstantiatedTypeEnvString Γ : @InstantiatedTypeEnv nat Γ := count (length Γ).
  Definition InstantiatedCoercionEnvString Γ Δ : @InstantiatedCoercionEnv nat nat Γ Δ := count (length Δ).
  Definition judgment2latex (j:Judg) : string :=
      match j with
        | mkJudg Γ Δ  a b =>
          let Γ' := InstantiatedTypeEnvString Γ in
          let Δ' := InstantiatedCoercionEnvString Γ Δ in
          let lt2l := fun nt:nat*(LeveledHaskType Γ) => 
            let (n,lt) := nt in
              match lt with
                t @@ l =>
                (var2string n)+++"{:}"+++(@ltype2latex Γ (t nat Γ') (map (fun x:HaskTyVar Γ => x nat Γ') l))
              end in
          let lt2l' := fun lt:(LeveledHaskType Γ) => 
              match lt with
                t @@ l =>
                "e{:}"+++(@ltype2latex Γ (t nat Γ') (map (fun x:HaskTyVar Γ => x nat Γ') l))
              end in
          (list2latex "" lt2l "\ ,\ " (enumerate (leaves a)))
          +++" \ \vdash_e\  "(*+++"e{:}"*)
          +++(list2latex "" lt2l' "\ ,\ " (leaves b))
      end.

  Definition j2l (j2j:Judg -> Judg) jt :=
    @judgments2latex Judg judgment2latex (mapOptionTree j2j jt).

  Fixpoint nd_urule2latex {Γ}{Δ}{h}{c}(r:@URule Γ Δ h c) : string :=
    match r with
      | (RLeft   _ _  c r  ) => nd_urule2latex r
      | (RRight   _ _ c r  ) => nd_urule2latex r
      | (RCanL   t a       ) => "CanL"
      | (RCanR   t a       ) => "CanR"
      | (RuCanL  t a       ) => "uCanL"
      | (RuCanR  t a       ) => "uCanR"
      | (RAssoc  t a b c   ) => "Assoc"
      | (RCossa  t a b c   ) => "Cossa"
      | (RExch   t a b     ) => "Exch"
      | (RWeak   t a       ) => "Weak"
      | (RCont   t a       ) => "Cont"
    end.

  Fixpoint nd_rule2latex {h}{c}(r:Rule h c) : string :=
    match r with
      | RURule _ _ _ _ r => nd_urule2latex r
      | RNote   x n z        => "Note"
      | RLit    Γ _ l     _    => "Lit"
      | RVar    Γ _ σ         p => "Var"
      | RLam    Γ _ Σ tx te   p x => "Abs"
      | RCast   Γ _ Σ σ τ γ   p x => "Cast"
      | RAbsT   Γ  Σ κ σ a   p    => "AbsT"
      | RAppT   Γ _  Σ κ σ τ   p y => "AppT"
      | RAppCo  Γ _ Σ κ _ σ₁ σ₂ σ γ p  => "AppCo"
      | RAbsCo  Γ  Σ κ σ cc σ₁ σ₂ p y q  => "AbsCo"
      | RApp    Γ _ Σ₁ Σ₂ tx te p => "App"
      | RLet    Γ _ Σ₁ Σ₂ σ₁ σ₂ p => "Let"
      | REmptyGroup _ a => "REmptyGroup"
      | RBindingGroup _ a b c d e => "RBindingGroup"
      | RLetRec Γ _ p lri q  => "LetRec"
      | RCase   Σ Γ T κlen κ  ldcd τ  _ _ => "Case"
      | RBrak   Σ _ a b c _ => "Brak"
      | REsc   Σ _ a b c _ => "Esc"
  end.

  Fixpoint nd_hideURule {Γ}{Δ}{h}{c}(r:@URule Γ Δ h c) : bool :=
    match r with
      | RLeft  h c ctx r   => nd_hideURule r
      | RRight h c ctx r   => nd_hideURule r
      | RCanL   t a        => true
      | RCanR   t a        => true
      | RuCanL  t a        => true
      | RuCanR  t a        => true
      | RAssoc  t a b c    => true
      | RCossa  t a b c    => true
      | RExch   t (T_Leaf None) b     => true
      | RExch   t a  (T_Leaf None)    => true
      | RWeak   t (T_Leaf None)       => true
      | RCont   t (T_Leaf None)       => true
      | _ => false
    end.
  Fixpoint nd_hideRule {h}{c}(r:Rule h c) : bool :=
    match r with
      | RURule _ _ _ _ r => nd_hideURule r
      | REmptyGroup a _ => true
      | RBindingGroup _ _ _ _ _ _  => true
      | _ => false
    end.
End ToLatex.

Axiom systemfc_all_rules_one_conclusion : forall h c1 c2 (r:Rule h (c1,,c2)), False.

Definition nd_ml_toLatex {c}(pf:@ND _ Rule [] c) :=
  @SCND_toLatex _ _
      judgment2latex
      (fun h c r => @nd_rule2latex h c r)
      (fun h c r => @nd_hideRule h c r)
      _ _ (mkSCND (systemfc_all_rules_one_conclusion) _ _ _ pf (scnd_weak [])).
