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
Require Import HaskKinds.
Require Import HaskWeakVars.
Require Import HaskWeakTypes.
Require Import HaskLiteralsAndTyCons.
Require Import HaskStrongTypes.
Require Import HaskStrong.
Require Import HaskProof.
Require Import HaskCoreTypes.

Open Scope string_scope.
Section ToLatex.

  Fixpoint kind2latex (k:Kind) : string :=
    match k with
    | ★                            => "\star"
    | ★  ⇛ k2                      => "\star\Rightarrow "+++kind2latex k2
    | k1 ⇛ k2                      => "("+++kind2latex k1+++")\Rightarrow "+++kind2latex k2
    | KindUnliftedType             => "\text{\tt{\#}}"
    | KindUnboxedTuple             => "\text{\tt{(\#)}}"
    | KindArgType                  => "\text{\tt{??}}"
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
      | S (S (S (S (S (S (S (S (S (S (S x)))))))))) => "z_{"+++x+++"}"
    end.
  Close Scope nat_scope.

  Definition tyvar2greek (n:nat) :=
    match n with
      | O => "\alpha"
      | S O => "\beta"
      | S (S O) => "\xi"
      | S (S (S n)) => "\alpha_{"+++n+++"}"
    end.

  Definition covar2greek (n:nat) :=
    "{\gamma_{"+++n+++"}}".

  (* TODO: now that PHOAS tyvar-representation-types are kind-indexed, we can do some clever stuff here *)
  Fixpoint type2latex (needparens:bool)(n:nat){κ}(t:RawHaskType (fun _ => nat) κ) {struct t} : string :=
    match t with
    | TVar    _ v          => tyvar2greek v
    | TCon    tc           => "\text{\tt{"+++sanitizeForLatex (toString tc) +++"}}"
    | TCoerc _ t1 t2   t   => "{("+++type2latex false n t1+++"{\sim}"
                                  +++type2latex false n t2+++")}\Rightarrow{"
                                  +++type2latex needparens n t+++"}"
    | TApp  _ _  t1 t2     =>
      match t1 with
        | TApp _ _ TArrow t1 =>
                     if needparens
                     then "("+++(type2latex true n t1)+++"{\rightarrow}"+++(type2latex true n t2)+++")"
                     else (type2latex true n t1)+++"{\rightarrow}"+++(type2latex true n t2)
        | _ =>
                     if needparens
                     then "("+++(type2latex true n t1)+++" "+++(type2latex false n t2)+++")"
                     else (type2latex true n t1)+++" "+++(type2latex false n t2)
      end
    | TArrow => "\text{\tt{(->)}}"
    | TAll   k f           => let alpha := tyvar2greek n
                              in "(\forall "+++ alpha +++ "{:}"+++ kind2latex k +++")"+++
                                   type2latex false (S n) (f n)
    | TCode  ec t          => "\code{"+++(type2latex true n ec)+++"}{"+++(type2latex false n t)+++"}"
    | TyFunApp   tfc lt    => "{\text{\tt{"+++sanitizeForLatex (toString tfc) +++"}}}"+++
                              "_{"+++n+++"}"+++
                              fold_left (fun x y => " \  "+++x+++y)
                              (typeList2latex false n lt) ""
  end
  with typeList2latex (needparens:bool)(n:nat){κ}(t:RawHaskTypeList κ) {struct t} : list string :=
  match t with
  | TyFunApp_nil                 => nil
  | TyFunApp_cons  κ kl rhk rhkl => (type2latex needparens n rhk)::(typeList2latex needparens n rhkl)
  end.

  Definition ltype2latex {Γ:TypeEnv}{κ}(t:RawHaskType (fun _ => nat) κ)(lev:list nat) : string :=
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

  Fixpoint count (n:nat) : vec nat n :=
  match n with
    | O    => vec_nil
    | S n' => n':::(count n')
  end.

  Fixpoint count' (lk:list Kind)(n:nat) : IList _ (fun _ => nat) lk :=
  match lk as LK return IList _ _ LK with
    | nil    => INil
    | h::t   => n::::(count' t (S n))
  end.

  Definition InstantiatedTypeEnvString     Γ   : @InstantiatedTypeEnv     (fun _ => nat) Γ := count' Γ O.
  Definition InstantiatedCoercionEnvString Γ Δ : @InstantiatedCoercionEnv (fun _ => nat) nat Γ Δ  := count (length Δ).
  Definition judgment2latex (j:Judg) : string :=
      match j with
        | mkJudg Γ Δ  a b =>
          let Γ' := InstantiatedTypeEnvString Γ in
          let Δ' := InstantiatedCoercionEnvString Γ Δ in
          let lt2l := fun nt:nat*(LeveledHaskType Γ ★) => 
            let (n,lt) := nt in
              match lt with
                t @@ l =>
                (var2string n)+++"{:}"+++(@ltype2latex Γ _ (t (fun _ => nat) Γ')
                  (map (fun x:HaskTyVar Γ _ => x (fun _ => nat) Γ') l))
              end in
          let lt2l' := fun lt:(LeveledHaskType Γ ★) => 
              match lt with
                t @@ l =>
                "e{:}"+++(@ltype2latex Γ _ (t (fun _ => nat) Γ')
                  (map (fun x:HaskTyVar Γ _ => x (fun _ => nat) Γ') l))
              end in
          (list2latex "" lt2l "\ ,\ " (enumerate (leaves a)))
          +++" \ \vdash_e\  "(*+++"e{:}"*)
          +++(list2latex "" lt2l' "\ ,\ " (leaves b))
      end.

  Definition j2l (j2j:Judg -> Judg) jt :=
    @judgments2latex Judg judgment2latex (mapOptionTree j2j jt).

  Fixpoint nd_urule2latex {Γ}{Δ}{h}{c}(r:@URule Γ Δ h c) : string :=
    match r with
      | RLeft   _ _ _ r => nd_urule2latex r
      | RRight  _ _ _ r => nd_urule2latex r
      | RCanL   _ _     => "CanL"
      | RCanR   _ _     => "CanR"
      | RuCanL  _ _     => "uCanL"
      | RuCanR  _ _     => "uCanR"
      | RAssoc  _ _ _ _ => "Assoc"
      | RCossa  _ _ _ _ => "Cossa"
      | RExch   _ _ _   => "Exch"
      | RWeak   _ _     => "Weak"
      | RCont   _ _     => "Cont"
    end.

  Fixpoint nd_rule2latex {h}{c}(r:Rule h c) : string :=
    match r with
      | RURule        _ _ _ _ r         => nd_urule2latex r
      | RNote         _ _ _ _ _ _       => "Note"
      | RLit          _ _ _ _           => "Lit"
      | RVar          _ _ _ _           => "Var"
      | RGlobal       _ _ _ _ _         => "Global"
      | RLam          _ _ _ _ _ _       => "Abs"
      | RCast         _ _ _ _ _ _ _     => "Cast"
      | RAbsT         _ _ _ _ _ _       => "AbsT"
      | RAppT         _ _ _ _ _ _ _     => "AppT"
      | RAppCo        _ _ _ _ _ _ _ _ _ => "AppCo"
      | RAbsCo        _ _ _ _ _ _ _ _   => "AbsCo"
      | RApp          _ _ _ _ _ _ _     => "App"
      | RLet          _ _ _ _ _ _ _     => "Let"
      | RBindingGroup _ _ _ _ _ _       => "RBindingGroup"
      | RLetRec       _ _ _ _ _ _       => "LetRec"
      | RCase         _ _ _ _ _ _ _ _   => "Case"
      | RBrak         _ _ _ _ _ _       => "Brak"
      | REsc          _ _ _ _ _ _       => "Esc"
      | REmptyGroup   _ _               => "REmptyGroup"
  end.

  Fixpoint nd_hideURule {Γ}{Δ}{h}{c}(r:@URule Γ Δ h c) : bool :=
    match r with
      | RLeft   _ _ _ r               => nd_hideURule r
      | RRight  _ _ _ r               => nd_hideURule r
      | RCanL   _ _                   => true
      | RCanR   _ _                   => true
      | RuCanL  _ _                   => true
      | RuCanR  _ _                   => true
      | RAssoc  _ _ _ _               => true
      | RCossa  _ _ _ _               => true
      | RExch   _    (T_Leaf None) b  => true
      | RExch   _ a  (T_Leaf None)    => true
      | RWeak   _    (T_Leaf None)    => true
      | RCont   _    (T_Leaf None)    => true
      | _                             => false
    end.
  Fixpoint nd_hideRule {h}{c}(r:Rule h c) : bool :=
    match r with
      | RURule        _ _ _ _ r   => nd_hideURule r
      | REmptyGroup   _ _         => true
      | RBindingGroup _ _ _ _ _ _ => true
      | _                         => false
    end.
End ToLatex.

Definition nd_ml_toLatex {c}(pf:@ND _ Rule [] c) :=
  @SCND_toLatex _ _
      judgment2latex
      (fun h c r => @nd_rule2latex h c r)
      (fun h c r => @nd_hideRule h c r)
      _ _ (mkSCND (systemfc_all_rules_one_conclusion) _ _ _ pf (scnd_weak [])).
