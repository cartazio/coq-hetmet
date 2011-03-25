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
Section HaskProofToLatex.

  Context {TV:Kind -> Type}.
  Context {TVLatex:forall k, ToLatex (TV k)}.
  Context {freshM:FreshMonad (∀ κ, TV κ)}.
  Definition FreshM' := FMT freshM.
  Instance FreshMon' : Monad FreshM' := FMT_Monad freshM.
  
  Instance ToLatexTyCon : ToLatex TyCon.
    admit.
    Defined.

  Fixpoint typeToLatex (needparens:bool){κ}(t:RawHaskType TV κ) {struct t} : FMT freshM Latex :=
    match t with
    | TVar    _ v        => return toLatex v
    | TCon    tc         => return (latex "\text{\tt{")+=+tc+=+(latex "}}")
    | TArrow             => return latex "\text{\tt{(->)}}"
    | TCoerc _ t1 t2   t => bind t1' = typeToLatex false      t1
                          ; bind t2' = typeToLatex false      t2
                          ; bind t'  = typeToLatex needparens t
                          ; return (latex "{(")+=+t1'+=+(latex "{\sim}")+=+
                                     t2'+=+(latex ")}\Rightarrow{")+=+t'+=+(latex "}")
    | TApp  _ _  t1 t2   => match t1 with
                            | TApp _ _ TArrow tx => bind t1' = typeToLatex true tx
                                                  ; bind t2' = typeToLatex true t2
                                                  ; let body := t1'+=+(latex "{\rightarrow}")+=+t2'
                                                    in return if needparens then (latex "(")+=+body+=+(latex ")") else body
                            | _                  => bind t1' = typeToLatex true t1
                                                  ; bind t2' = typeToLatex true t2
                                                  ; let body := t1'+=+(latex " ")+=+t2'
                                                    in return if needparens then (latex "(")+=+body+=+(latex ")") else body
                         end
    | TCode  ec t        => bind ec' = typeToLatex true ec
                          ; bind t'  = typeToLatex false t
                          ; return (latex "\code{")+=+ec'+=+(latex "}{")+=+t'+=+(latex "}")
    | TyFunApp   tfc lt  => bind rest = typeListToLatex false lt
                          ; return (latex "{\text{\tt{")+=+(sanitizeForLatex (toString tfc))+=+(latex "}}}")+=+
                                   (*(latex "_{")+=+(latex (toString (tfc:nat)))+=+(latex "}")+=+*)
                                   (fold_left (fun x y => (latex " \  ")+=+x+=+y)
                                     rest (latex ""))
    | TAll   k f         => (*bind alpha = next
                          ; bind t'    = typeToLatex false (f (alpha k))
                          ; *)return (latex "(\forall ")(*+=+(@toLatex _ (TVLatex k) (alpha k))*)
                          +=+(latex "{:}")+=+(kindToLatex k)+=+(latex ")")(*+=+t'*)
  end
  with typeListToLatex (needparens:bool){κ}(t:RawHaskTypeList κ) {struct t} : FreshM' (list Latex) :=
  match t with
  | TyFunApp_nil                 => return nil
  | TyFunApp_cons  κ kl rhk rhkl => bind r  = typeToLatex needparens rhk
                                  ; bind rl = typeListToLatex needparens rhkl
                                  ; return (r::rl)
  end.
(*
  Definition ltypeToLatex {Γ:TypeEnv}{κ}(t:RawHaskType TV κ)(lev:list nat) : FreshM' Latex :=
    match lev with
      | nil => typeToLatex false t
      | lv  => bind t' = typeToLatex true t
             ; 
        (latex "{")
        +=+
        
        +=+
        (latex "}^{")
        +=+
        (fold_left (fun x y => x+=+":"+=+y) (map tyvar2greek lv) "")+=+"}"
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

  Definition covar2greek (n:nat) :=
    "{\gamma_{"+++n+++"}}".

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
  Definition judgmentToLatex (j:Judg) : string :=
      match j with
        | mkJudg Γ Δ  a b =>
          let Γ' := InstantiatedTypeEnvString Γ in
          let Δ' := InstantiatedCoercionEnvString Γ Δ in
          let lt2l := fun nt:nat*(LeveledHaskType Γ ★) => 
            let (n,lt) := nt in
              match lt with
                t @@ l =>
                (var2string n)+++"{:}"+++(@ltypeToLatex Γ _ (t (fun _ => nat) Γ')
                  (map (fun x:HaskTyVar Γ _ => x (fun _ => nat) Γ') l))
              end in
          let lt2l' := fun lt:(LeveledHaskType Γ ★) => 
              match lt with
                t @@ l =>
                (@ltypeToLatex Γ _ (t (fun _ => nat) Γ')
                  (map (fun x:HaskTyVar Γ _ => x (fun _ => nat) Γ') l))
              end in
          (listToLatex "" lt2l "\ ,\ " (enumerate (leaves a)))
          +++" \ \vdash_e\  "(*+++"e{:}"*)
          +++(listToLatex "" lt2l' "\ ,\ " (leaves b))
      end.

  Definition j2l (j2j:Judg -> Judg) jt :=
    @judgmentsToLatex Judg judgmentToLatex (mapOptionTree j2j jt).

  Fixpoint nd_uruleToLatex {Γ}{Δ}{h}{c}(r:@URule Γ Δ h c) : string :=
    match r with
      | RLeft   _ _ _ r => nd_uruleToLatex r
      | RRight  _ _ _ r => nd_uruleToLatex r
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

  Fixpoint nd_ruleToLatex {h}{c}(r:Rule h c) : string :=
    match r with
      | RURule        _ _ _ _ r         => nd_uruleToLatex r
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
  *)

End HaskProofToLatex.

(*
Definition nd_ml_toLatex {c}(pf:@ND _ Rule [] c) :=
  @SCND_toLatex _ _
      judgmentToLatex
      (fun h c r => @nd_ruleToLatex h c r)
      (fun h c r => @nd_hideRule h c r)
      _ _ (mkSCND (systemfc_all_rules_one_conclusion) _ _ _ pf (scnd_weak [])).
*)