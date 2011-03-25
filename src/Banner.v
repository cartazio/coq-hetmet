(***********************************************************************************************************************************
 *
 * This is the Coq development accompanying
 *
 *   __Multi-Level Programs are Generalized Arrows__
 *
 * Best viewed on a 132-character-wide display (use the first line of this file to size your window)
 *
 * This file makes extensive use of Unicode (UTF-8); please make sure your text editor supports it.
 *
 * Here is the version of Coq I used:
 * 
 *   megacz@skolem:~$ coqc -v
 *   The Coq Proof Assistant, version 8.3pl1 (March 2011)
 *   compiled on Mar 17 2011 21:07:25 with OCaml 3.11.2
 *
 * Warning: this script may take a half-hour or more to typecheck, even on a very fast machine.
 *          It also needs about 1.5GB of ram; if you have less than that it will run unbearably slowly.
 *
 *  I recommend checking it using the following command:
 *
 *    coqc -noglob -dont-load-proofs GArrows.v
 *
 **********************************************************************************************************************************)

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Setoid.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Omega.
