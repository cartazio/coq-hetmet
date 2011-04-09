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

Require Import Notations.
Export Notations.

Set Printing Width 130.       (* Proof General seems to add an extra two columns of overhead *)
Generalizable All Variables.

Reserved Notation "a ** b"                      (at level 40).
Reserved Notation "a ;; b"                      (at level 45).

Reserved Notation "a -~- b"                     (at level 10).
Reserved Notation "pf1 === pf2"                 (at level 80).
Reserved Notation "?? x"                        (at level 1).
Reserved Notation "a ,, b"                      (at level 50).
Reserved Notation "!! f"                        (at level 3).
Reserved Notation "!` x"                        (at level 2).
Reserved Notation "`! x"                        (at level 2).
Reserved Notation "[# f #]"                     (at level 2).
Reserved Notation "a ---> b"                    (at level 11, right associativity).
Reserved Notation "a <- b"                      (at level 100, only parsing).
Reserved Notation "G |= S"                      (at level 75).
Reserved Notation "a :: b"                      (at level 60, right associativity).
Reserved Notation "a ++ b"                      (at level 60, right associativity).
Reserved Notation "<[ t @]>"                    (at level 30).
Reserved Notation "<[ t @ n ]>"                 (at level 30).
Reserved Notation "<[ e ]>"                     (at level 30).
Reserved Notation "R ==> R' "                   (at level 55, right associativity).
Reserved Notation "a ==[ n ]==> b"              (at level 20).
Reserved Notation "a ==[ h | c ]==> b"          (at level 20).
Reserved Notation "H /⋯⋯/ C"                    (at level 70).
Reserved Notation "a |== b @@ c"                (at level 100).
Reserved Notation "a >>[ n ]<< b"               (at level 100).

Reserved Notation "'<[' a '|-' t ']>'"          (at level 35).

Reserved Notation "Γ '∌'    x"                  (at level 10).
Reserved Notation "Γ '∌∌'   x"                  (at level 10).
Reserved Notation "Γ '∋∋'   x : a ∼ b"          (at level 10, x at level 99).
Reserved Notation "Γ '∋'    x : c"              (at level 10, x at level 99).

Reserved Notation "a ⇛ b"                       (at level 55, right associativity).
Reserved Notation "φ₁ →→ φ₂"                    (at level 11, right associativity).
Reserved Notation "a '⊢ᴛy'  b : c"              (at level 20, b at level 99, c at level 80).
Reserved Notation "a '⊢ᴄᴏ'  b : c ∼ d"          (at level 20, b at level 99).
Reserved Notation "Γ '+'    x : c"              (at level 50, x at level 99).
Reserved Notation "Γ '++'   x : a ∼ b"          (at level 50, x at level 99).
Reserved Notation "φ₁ ∼∼ φ₂ ⇒ φ₃"               (at level 11, φ₂ at level 99, right associativity).

Notation "?? T" := (option T).
Reserved Notation "Γ > past : present '⊢ᴇ' succedent"
   (at level 52, past at level 99, present at level 50, succedent at level 50).

Reserved Notation "'η'".
Reserved Notation "'★'".

Close Scope nat_scope.  (* so I can redefine '1' *)

Delimit Scope arrow_scope   with arrow.
Delimit Scope biarrow_scope with biarrow.
Delimit Scope garrow_scope  with garrow.

