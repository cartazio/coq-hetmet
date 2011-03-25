(*********************************************************************************************************************************)
(* NaturalDeductionToLatex: rendering natural deduction proofs as LaTeX code                                                     *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import NaturalDeduction.

Section ToLatex.

  Context {Judgment : Type}.
  Context {Rule     : forall (hypotheses:Tree ??Judgment)(conclusion:Tree ??Judgment), Type}.
  Context {JudgmentToLatexMath : ToLatexMath Judgment}.
  Context {RuleToLatexMath     : forall h c, ToLatexMath (Rule h c)}.
  
  Open Scope string_scope.

  Definition judgments2latex (j:Tree ??Judgment) := treeToLatexMath (mapOptionTree toLatexMath j).

  Definition eolL : LatexMath := rawLatexMath eol.

  (* invariant: each proof shall emit its hypotheses visibly, except nd_id0 *)
  Section SCND_toLatex.

    (* indicates which rules should be hidden (omitted) from the rendered proof; useful for structural operations *)
    Context (hideRule : forall h c (r:Rule h c), bool).

    Fixpoint SCND_toLatexMath {h}{c}(pns:SCND(Rule:=Rule) h c) : LatexMath :=
      match pns with
        | scnd_leaf   ht c pn            => SCND_toLatexMath pn
        | scnd_branch ht c1 c2 pns1 pns2 => SCND_toLatexMath pns1 +++ rawLatexMath " \hspace{1cm} " +++ SCND_toLatexMath pns2
        | scnd_weak     c                => rawLatexMath ""
        | scnd_comp ht ct c pns rule     => if hideRule _ _ rule
                                            then SCND_toLatexMath pns
                                            else rawLatexMath "\trfrac["+++ toLatexMath rule +++ rawLatexMath "]{" +++ eolL +++
                                              SCND_toLatexMath pns +++ rawLatexMath "}{" +++ eolL +++
                                              toLatexMath c +++ rawLatexMath "}" +++ eolL
      end.
  End SCND_toLatex.

  (* this is a work-in-progress; please use SCND_toLatexMath for now *)
  Fixpoint nd_toLatexMath {h}{c}(nd:@ND _ Rule h c)(indent:string) :=
    match nd with
      | nd_id0                      => rawLatexMath indent +++
                                       rawLatexMath "% nd_id0 " +++ eolL
      | nd_id1  h'                  => rawLatexMath indent +++
                                       rawLatexMath "% nd_id1 "+++ judgments2latex h +++ eolL
      | nd_weak h'                  => rawLatexMath indent +++
                                       rawLatexMath "\inferrule*[Left=ndWeak]{" +++ toLatexMath h' +++ rawLatexMath "}{ }" +++ eolL
      | nd_copy h'                  => rawLatexMath indent +++
                                       rawLatexMath "\inferrule*[Left=ndCopy]{"+++judgments2latex h+++
                                                         rawLatexMath "}{"+++judgments2latex c+++rawLatexMath "}" +++ eolL
      | nd_prod h1 h2 c1 c2 pf1 pf2 => rawLatexMath indent +++
                                       rawLatexMath "% prod " +++ eolL +++
                                       rawLatexMath indent +++
                                       rawLatexMath "\begin{array}{c c}" +++ eolL +++
                                       (nd_toLatexMath pf1 ("  "+++indent)) +++
                                       rawLatexMath indent +++
                                       rawLatexMath " & " +++ eolL +++
                                       (nd_toLatexMath pf2 ("  "+++indent)) +++
                                       rawLatexMath indent +++
                                       rawLatexMath "\end{array}"
      | nd_comp h  m     c  pf1 pf2 => rawLatexMath indent +++
                                       rawLatexMath "% comp " +++ eolL +++
                                       rawLatexMath indent +++
                                       rawLatexMath "\begin{array}{c}" +++ eolL +++
                                       (nd_toLatexMath pf1 ("  "+++indent)) +++
                                       rawLatexMath indent +++
                                       rawLatexMath " \\ " +++ eolL +++
                                       (nd_toLatexMath pf2 ("  "+++indent)) +++
                                       rawLatexMath indent +++
                                       rawLatexMath "\end{array}"
      | nd_cancell a                => rawLatexMath indent +++
                                       rawLatexMath "% nd-cancell " +++ (judgments2latex a) +++ eolL
      | nd_cancelr a                => rawLatexMath indent +++
                                       rawLatexMath "% nd-cancelr " +++ (judgments2latex a) +++ eolL
      | nd_llecnac a                => rawLatexMath indent +++
                                       rawLatexMath "% nd-llecnac " +++ (judgments2latex a) +++ eolL
      | nd_rlecnac a                => rawLatexMath indent +++
                                       rawLatexMath "% nd-rlecnac " +++ (judgments2latex a) +++ eolL
      | nd_assoc   a b c            => rawLatexMath ""
      | nd_cossa   a b c            => rawLatexMath ""
      | nd_rule    h c r            => toLatexMath r
    end.

End ToLatex.
