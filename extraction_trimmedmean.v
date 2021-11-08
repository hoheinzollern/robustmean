From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg matrix.
From mathcomp Require Import all_algebra. (* for GRing.Theory *)
From mathcomp Require boolp classical_sets. (* classical_sets for pointedType *)
From mathcomp Require Import Rstruct topology. (* topology for fct_ringType *)
Require Import Reals Lra ROrderedType.
From infotheo Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext.
From infotheo Require Import Rbigop proba fdist.
Require Import List.
Require Import Sorting.
Require Orders.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope proba_scope.
Local Open Scope R_scope.


Definition Average l := fold_left Rplus l 0 / INR (length l).

Module ROrder <: Orders.TotalLeBool.
Definition t := R.
Definition leb := Rleb.
Lemma leb_total  (x y : t) : leb x y = true \/ leb y x = true.
Proof.
    intros.
    unfold leb, Rleb.
    destruct (Rle_dec x y).
    - by [left].
    - destruct (total_order_T x y).
      - left. destruct n, s; lra.
      - right. destruct (Rle_dec y x); lra.
  Qed.
End ROrder.

Module RSort := Sort ROrder.

Definition SortedList l := RSort.sort l.

(*Given function (take the min(head) element of sorted list), list l and number of times, do Trim*)
Fixpoint TrimLeft (l: list R) n := match n with
  | 0 => l
  | S n' => TrimLeft (tl l) n'
end.

(*Given function (take the max(last) element of sorted list), list l and number of times, do Trim*)
Fixpoint TrimRight (l: list R) n := match n with
  | 0 => l
  | S n' => TrimRight (removelast l) n'
end.

Definition TrimmedMean l eps :=
    let n_rm := Z.to_nat (ceil (2 * eps * INR(length l))) in
    let l' := SortedList l in
    let l''  := TrimLeft l' n_rm in
    let l''' := TrimRight l'' n_rm in
    Average l'''.

Require Extraction.
Extraction Language Haskell.
Extraction "trimmedmean.hs" TrimmedMean.
