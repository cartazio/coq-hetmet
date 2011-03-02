(*********************************************************************************************************************************)
(* Preamble: miscellaneous notations                                                                                             *)
(*********************************************************************************************************************************)

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Setoid.
Require Import Coq.Strings.String.
Export Coq.Unicode.Utf8.
Export Coq.Classes.RelationClasses.
Export Coq.Classes.Morphisms.
Export Coq.Setoids.Setoid.

Set Printing Width 130.       (* Proof General seems to add an extra two columns of overhead *)
Generalizable All Variables.

Reserved Notation "a -~- b"                     (at level 10).
Reserved Notation "a ** b"                      (at level 10).
Reserved Notation "?? x"                        (at level 1).
Reserved Notation "a ,, b"                      (at level 50).
Reserved Notation "!! f"                        (at level 3).
Reserved Notation "!` x"                        (at level 2).
Reserved Notation "`! x"                        (at level 2).
Reserved Notation "a  ~=>  b"                   (at level 70, right associativity).
Reserved Notation "H ===> C"                    (at level 100).
Reserved Notation "f >>=>> g"                   (at level 45).
Reserved Notation "a ~~{ C }~~> b"              (at level 100).
Reserved Notation "f <--> g"                    (at level 20).
Reserved Notation "! f"                         (at level 2).
Reserved Notation "? f"                         (at level 2).
Reserved Notation "# f"                         (at level 2).
Reserved Notation "f '⁻¹'"                      (at level 1).
Reserved Notation "a ≅ b"                       (at level 70, right associativity).
Reserved Notation "C 'ᵒᴾ'"                      (at level 1).
Reserved Notation "F \ a"                       (at level 20).
Reserved Notation "f >>> g"                     (at level 45).
Reserved Notation "a ~~ b"                      (at level 54).
Reserved Notation "a ~> b"                      (at level 70, right associativity).
Reserved Notation "a ≃ b"                       (at level 70, right associativity).
Reserved Notation "a ≃≃ b"                      (at level 70, right associativity).
Reserved Notation "a ~~> b"                     (at level 70, right associativity).
Reserved Notation "F  ~~~> G"                   (at level 70, right associativity).
Reserved Notation "F <~~~> G"                   (at level 70, right associativity).
Reserved Notation "a ⊗ b"                       (at level 40).
Reserved Notation "a ⊗⊗ b"                      (at level 40).
Reserved Notation "a ⊕  b"                      (at level 40).
Reserved Notation "a ⊕⊕ b"                      (at level 40).
Reserved Notation "f ⋉ A"                       (at level 40).
Reserved Notation "A ⋊ f"                       (at level 40).
Reserved Notation "- ⋉ A"                       (at level 40).
Reserved Notation "A ⋊ -"                       (at level 40).
Reserved Notation "a *** b"                     (at level 40).
Reserved Notation "a ;; b"                      (at level 45).
Reserved Notation "[# f #]"                     (at level 2).
Reserved Notation "a ---> b"                    (at level 11, right associativity).
Reserved Notation "a <- b"                      (at level 100, only parsing).
Reserved Notation "G |= S"                      (at level 75).
Reserved Notation "F -| G"                      (at level 75).
Reserved Notation "a :: b"                      (at level 60, right associativity).
Reserved Notation "a ++ b"                      (at level 60, right associativity).
Reserved Notation "<[ t @]>"                    (at level 30).
Reserved Notation "<[ t @ n ]>"                 (at level 30).
Reserved Notation "<[ e ]>"                     (at level 30).
Reserved Notation "'Λ' x : t :-> e"             (at level 9, right associativity, x ident).
Reserved Notation "R ==> R' "                   (at level 55, right associativity).
Reserved Notation "f ○ g"                       (at level 100).
Reserved Notation "a ==[ n ]==> b"              (at level 20).
Reserved Notation "a ==[ h | c ]==> b"          (at level 20).
Reserved Notation "H /⋯⋯/ C"                    (at level 70).
Reserved Notation "pf1 === pf2"                 (at level 80).
Reserved Notation "a |== b @@ c"                (at level 100).
Reserved Notation "f >>>> g"                    (at level 45).
Reserved Notation "a >>[ n ]<< b"               (at level 100).
Reserved Notation "f **** g"                    (at level 40).
Reserved Notation "C × D"                       (at level 40).
Reserved Notation "C ×× D"                      (at level 45).
Reserved Notation "C ⁽ºᑭ⁾"                      (at level 1).

Reserved Notation "'<[' a '|-' t ']>'"          (at level 35).

Reserved Notation "Γ '∌'    x"                  (at level 10).
Reserved Notation "Γ '∌∌'   x"                  (at level 10).
Reserved Notation "Γ '∋∋'   x : a ∼ b"          (at level 10, x at level 99).
Reserved Notation "Γ '∋'    x : c"              (at level 10, x at level 99).

Reserved Notation "a ⇛ b"                       (at level 40).
Reserved Notation "φ₁ →→ φ₂"                    (at level 11, right associativity).
Reserved Notation "a '⊢ᴛy'  b : c"              (at level 20, b at level 99, c at level 80).
Reserved Notation "a '⊢ᴄᴏ'  b : c ∼ d"          (at level 20, b at level 99).
Reserved Notation "Γ '+'    x : c"              (at level 50, x at level 99).
Reserved Notation "Γ '++'   x : a ∼ b"          (at level 50, x at level 99).
Reserved Notation "φ₁ ∼∼ φ₂ : κ ⇒ φ₃"           (at level 11, φ₂ at level 99, right associativity).

Reserved Notation "Γ > past : present '⊢ᴇ' succedent"
   (at level 52, past at level 99, present at level 50, succedent at level 50).

Reserved Notation "'η'".
Reserved Notation "'ε'".
Reserved Notation "'★'".

Notation "a +++ b" := (append a b) (at level 100).
Close Scope nat_scope.  (* so I can redefine '1' *)

Delimit Scope arrow_scope   with arrow.
Delimit Scope biarrow_scope with biarrow.
Delimit Scope garrow_scope  with garrow.

Notation "f ○ g"    := (fun x => f(g(x))).
Notation "?? T"     := (option T).

(* these are handy since Coq's pattern matching syntax isn't integrated with its abstraction binders (like Haskell and ML) *)
Notation "'⟨' x ',' y '⟩'" := ((x,y)) (at level 100).
Notation "'Λ' '⟨' x ',' y '⟩' e" := (fun xy => match xy with (a,b) => (fun x y => e) a b end) (at level 100).
Notation "'Λ' '⟨' x ',' '⟨' y ',' z '⟩' '⟩' e" :=
    (fun xyz => match xyz with (a,bc) => match bc with (b,c) => (fun x y z => e) a b c end end) (at level 100).
Notation "'Λ' '⟨' '⟨' x ',' y '⟩' ',' z '⟩' e" :=
    (fun xyz => match xyz with (ab,c) => match ab with (a,b) => (fun x y z => e) a b c end end) (at level 100).

Notation "∀ x y z u q , P" := (forall x y z u q , P)
  (at level 200, q ident, x ident, y ident, z ident, u ident, right associativity)
  : type_scope.
Notation "∀ x y z u q v , P" := (forall x y z u q v , P)
  (at level 200, q ident, x ident, y ident, z ident, u ident, v ident, right associativity)
  : type_scope.
Notation "∀ x y z u q v a , P" := (forall x y z u q v a , P)
  (at level 200, q ident, x ident, y ident, z ident, u ident, v ident, a ident, right associativity)
  : type_scope.
Notation "∀ x y z u q v a b , P" := (forall x y z u q v a b , P)
  (at level 200, q ident, x ident, y ident, z ident, u ident, v ident, a ident, b ident, right associativity)
  : type_scope.
Notation "∀ x y z u q v a b r , P" := (forall x y z u q v a b r , P)
  (at level 200, q ident, x ident, y ident, z ident, u ident, v ident, a ident, b ident, r ident, right associativity)
  : type_scope.
Notation "∀ x y z u q v a b r s , P" := (forall x y z u q v a b r s , P)
  (at level 200, q ident, x ident, y ident, z ident, u ident, v ident, a ident, b ident, r ident, s ident, right associativity)
  : type_scope.
Notation "∀ x y z u q v a b r s t , P" := (forall x y z u q v a b r s t , P)
  (at level 200, q ident, x ident, y ident, z ident, u ident, v ident, a ident, b ident, r ident, s ident, t ident,
    right associativity)
  : type_scope.
