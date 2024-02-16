From mathcomp Require Import all_ssreflect ssralg ssrnum matrix.
From mathcomp Require boolp.
From mathcomp Require Import Rstruct reals mathcomp_extra.
Require Import Reals Lra.
From infotheo Require Import ssrR Reals_ext realType_ext logb ssr_ext ssralg_ext.
From infotheo Require Import bigop_ext fdist proba.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Import Order.POrderTheory Order.Theory Num.Theory GRing.Theory.

Notation R := real_realType.

Section move_to_mathcomp.

Lemma setT_bool : [set: bool] = [set true; false].
Proof.
apply/eqP; rewrite eqEsubset; apply/andP; split => //.
by apply/subsetP => x; rewrite !inE; case: x.
Qed.

Lemma fsumr_gt0 (U : eqType) (F : U -> R) (s : seq U) :
  (0 < \sum_(i <- s) F i)%mcR -> exists2 i, i \in s & 0 < F i.
Proof.
elim: s => [|h t ih]; first by rewrite big_nil ltxx.
rewrite big_cons.
have H : forall x y : R, 0 < x + y -> 0 < x \/ 0 < y by move=> x y; lra.
move/RltP/H => [Fh0|]; first by exists h => //; rewrite mem_head.
by move/RltP/ih => [u ut Fu0]; exists u => //; rewrite inE ut orbT.
Qed.

End move_to_mathcomp.

Section move_to_infotheo.

Section nneg_finfun. (* Reals_ext.v *)
Local Open Scope R_scope.

Lemma nneg_finfun_ge0 (I : finType) (f : nneg_finfun I) i : (0 <= f i)%mcR.
Proof. by case: f => /= f /forallP /(_ i). Qed.

Lemma nneg_finfun_le0 (I : finType) (F : nneg_finfun I) i :
  (F i == 0) = (F i <= 0)%mcR.
Proof.
apply/idP/idP => [/eqP -> //|].
case: F => F /= /forallP /(_ i).
by rewrite eq_le coqRE => -> ->.
Qed.

Fail Check F : pos_fun _. (* Why no coercion pos_ffun >-> pos_fun? *)

Lemma pos_ffun_bigmaxR0P (I : finType) (r : seq I) (P : pred I) (F : nneg_finfun I) :
  reflect (forall i : I, i \in r -> P i -> F i = 0)
          (\rmax_(i <- r | P i) F i == 0).
Proof.
apply: (iffP idP) => [/eqP H i ir Pi|H].
- apply/eqP; rewrite nneg_finfun_le0 -coqRE -H.
  rewrite -big_filter; apply/RleP; apply: leR_bigmaxR.
  by rewrite mem_filter ir Pi.
- rewrite -big_filter big_seq.
  under eq_bigr=> i do rewrite mem_filter=> /andP [] /[swap] /(H i) /[apply] ->.
  by rewrite -big_seq big_const_seq iter_fix // maxRR.
Qed.

Lemma nnegP (U : finType) (C : {ffun U -> R}) :
  (forall u : U, 0 <= C u) -> [forall a, (0 <= C a)%mcR].
Proof. by move=> h; apply/forallP => u; apply/RleP. Qed.

Definition Cpos_fun (U : finType) (C : nneg_finfun U)
    (h : forall u : U, 0 <= C u) : nneg_finfun U :=
  mkNNFinfun (nnegP h).

End nneg_finfun.

Lemma pmax_eq0 [I : eqType] (r : seq I) [P : pred I] [F : I -> R] :
  (forall i, P i -> (0 <= F i)%mcR) ->
  ((\rmax_(i <- r | P i) F i)%mcR == 0%mcR) = all (fun i => P i ==> (F i == 0%mcR)) r.
Proof.
elim: r => /= [|h t ih PF0].
  by rewrite big_nil eqxx.
rewrite big_cons.
case: ifP => Ph.
  rewrite implyTb; apply/idP/andP.
    have [Fh|Fh] := leP (F h) (\rmax_(j <- t | P j) F j).
      rewrite Rmax_right//; last exact/RleP.
      move=> tPF; rewrite -ih//; split => //.
      by rewrite eq_le PF0// andbT -(eqP tPF).
    rewrite Rmax_left//; last exact/ltRW/RltP.
    move=> Fh0; rewrite Fh0; split => //.
    rewrite -ih// eq_le; apply/andP; split.
      by rewrite -(eqP Fh0); exact/RleP/ltRW/RltP.
    apply/RleP; rewrite -big_filter; apply/bigmaxR_ge0 => r.
    by rewrite mem_filter => /andP[/PF0 /RleP].
  move=> [/eqP Fh0 /allP tPF].
 rewrite Fh0; apply/eqP/Rmax_left; apply/leR_eqVlt; left.
 by apply/eqP; rewrite ih//; apply/allP.
by rewrite implyFb /= ih.
Qed.

Section bigmaxR.
Variables (A : eqType) (F : A -> R) (s : seq A).

Lemma leR_bigmaxR_P (P : pred A) : forall m, m \in s -> P m ->
  F m <= \rmax_(m <- s | P m) (F m).
Proof.
elim: s => // hd tl IH m; rewrite in_cons; case/orP.
- move/eqP => -> Pm; rewrite big_cons Pm; exact/leR_maxl.
- move/IH => H Pm; rewrite big_cons; case: ifPn => Phd; last exact: H.
  exact/(leR_trans (H Pm))/leR_maxr.
Qed.

Lemma bigmaxR_gt0 (P : pred A) :
  (exists i, [/\ i \in s, P i & 0 < F i]) -> 0 < \rmax_(m <- s | P m) (F m).
Proof.
by move=> [a [? ? Fa0]]; exact/(Rlt_le_trans _ _ _ Fa0)/leR_bigmaxR_P.
Qed.

End bigmaxR.

End move_to_infotheo.
