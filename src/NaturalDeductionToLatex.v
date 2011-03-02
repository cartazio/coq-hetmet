(*********************************************************************************************************************************)
(* NaturalDeductionToLatex: rendering natural deduction proofs as LaTeX code                                                     *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import NaturalDeduction.

(* string stuff *)
Variable eol : string.
Extract Constant eol  => "'\n':[]".

Section ToLatex.

  Context {Judgment : Type}.
  Context {Rule     : forall (hypotheses:Tree ??Judgment)(conclusion:Tree ??Judgment), Type}.

  (* the "user" must supply functions for latexifying judgments and rules *)
  Context (judgment2latex : Judgment -> string).
  Context (rule2latex     : forall h c, Rule h c -> string).
  
  Open Scope string_scope.
  Notation "a +++ b" := (append a b) (at level 100).
  Section TreeToLatex.
    Context (emptyleaf:string).
    Context {T:Type}.
    Context (leaf:T -> string).
    Fixpoint tree2latex' (j:Tree ??T) : string :=
      match j with
        | T_Leaf   None      => emptyleaf
        | T_Leaf   (Some j') => leaf j'
        | T_Branch b1 b2     => "\left["+++tree2latex' b1+++
                                "\text{\tt{,}}"+++
                                tree2latex' b2+++"\right]"
      end.
    Definition tree2latex (j:Tree ??T) : string :=
      match j with
        | T_Leaf   None      => emptyleaf
        | T_Leaf   (Some j') => leaf j'
        | T_Branch b1 b2     => tree2latex' b1+++
                                "\text{\tt{,}}"+++
                                tree2latex' b2
      end.
    Fixpoint list2latex (sep:string)(l:list T) : string :=
      match l with
        | nil      => emptyleaf
        | (a::nil) => leaf a
        | (a::b)   => (leaf a)+++sep+++(list2latex sep b)
      end.
  End TreeToLatex.

  Definition judgments2latex (j:Tree ??Judgment) := 
    list2latex " " judgment2latex " \\ " (leaves j).

  (* invariant: each proof shall emit its hypotheses visibly, except nd_id0 *)
  Section SCND_toLatex.
    Context (hideRule : forall h c (r:Rule h c), bool).

    Fixpoint SCND_toLatex {h}{c}(pns:SCND h c) : string :=
      match pns with
        | scnd_leaf   ht c pn            => SCND_toLatex pn
        | scnd_branch ht c1 c2 pns1 pns2 => SCND_toLatex pns1 +++ " \hspace{1cm} " +++ SCND_toLatex pns2
        | scnd_weak     c                => ""
        | scnd_axiom c               => judgment2latex c +++ eol
        | scnd_comp ht ct c pns rule => if hideRule _ _ rule
                                      then SCND_toLatex pns
                                      else "\trfrac["+++rule2latex _ _ rule +++ "]{" +++ eol +++
                                             SCND_toLatex pns +++ "}{" +++ eol +++
                                             judgment2latex c +++ "}" +++ eol
      end.
  End SCND_toLatex.

  (* FIXME: this doesn't actually work properly (but SCND_toLatex does!) *)
  Fixpoint nd_toLatex {h}{c}(nd:@ND _ Rule h c)(indent:string) :=
    match nd with
      | nd_id0                      => indent +++ "% nd_id0 " +++ eol
      | nd_id1  h'                  => indent +++ "% nd_id1 "+++ judgments2latex h +++ eol
      | nd_weak h'                  => indent +++ "\inferrule*[Left=ndWeak]{" +++ judgment2latex h' +++ "}{ }" +++ eol
      | nd_copy h'                  => indent +++ "\inferrule*[Left=ndCopy]{"+++judgments2latex h+++
                                                         "}{"+++judgments2latex c+++"}" +++ eol
      | nd_prod h1 h2 c1 c2 pf1 pf2 => indent +++ "% prod " +++ eol +++
                                       indent +++ "\begin{array}{c c}" +++ eol +++
                                       (nd_toLatex pf1 ("  "+++indent)) +++
                                       indent +++ " & " +++ eol +++
                                       (nd_toLatex pf2 ("  "+++indent)) +++
                                       indent +++ "\end{array}"
      | nd_comp h  m     c  pf1 pf2 => indent +++ "% comp " +++ eol +++
                                       indent +++ "\begin{array}{c}" +++ eol +++
                                       (nd_toLatex pf1 ("  "+++indent)) +++
                                       indent +++ " \\ " +++ eol +++
                                       (nd_toLatex pf2 ("  "+++indent)) +++
                                       indent +++ "\end{array}"
      | nd_cancell a                => indent +++ "% nd-cancell " +++ (judgments2latex a) +++ eol
      | nd_cancelr a                => indent +++ "% nd-cancelr " +++ (judgments2latex a) +++ eol
      | nd_llecnac a                => indent +++ "% nd-llecnac " +++ (judgments2latex a) +++ eol
      | nd_rlecnac a                => indent +++ "% nd-rlecnac " +++ (judgments2latex a) +++ eol
      | nd_assoc   a b c            => ""
      | nd_cossa   a b c            => ""
      | nd_rule    h c r            => rule2latex h c r
    end.

End ToLatex.
