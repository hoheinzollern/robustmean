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

Require Import Interval.Tactic.
Require Import Program.Wf.
Require Import robustmean util.

(**md**************************************************************************)
(* # lemmas 1.4, 1.5, etc.                                                    *)
(*                                                                            *)
(* This file contains a formalization of lemmas from the chapter 1 of         *)
(* Jacob Steinhardt, Robust learning: information theory and algorithms,      *)
(* PhD Standford 2018.                                                        *)
(*                                                                            *)
(* |   Definitions |    | Meaning                                            |*)
(* |---------------|----|----------------------------------------------------|*)
(* |       is_01 C | := | forall i, 0 <= C i <= 1                             *)
(* |    Weighted.d | == | given a distribution $d_0$ and a non-negative       *)
(* |               |    | function $g$, returns the distribution              *)
(* |               |    | $a\mapsto \frac{g(a) * d_0(a)}{\sum_b g(b) * d_0(b)}$ *)
(* |       Split.d | == | given a distribution $d_0$ and a non-negative       *)
(* |               |    | function $h$, returns the distribution              *)
(* |               |    | $\begin{array}{rl} (a,b) \mapsto & h(a) * d_0(a) \textrm{ if } b \\ & (1 - h(a))*d_0(a) \textrm{ o.w.}\end{array}$ *)
(* |      mean X A | := | `E_[X \| A]                                         *)
(* |      sq_dev X | == | "squared deviation": $(X - mean)^2$                 *)
(* |       var X A | := | `V_[X \| A]                                         *)
(* |         emean | == | empirical/estimate mean of the data,                *)
(* |               |    | weighted mean of all the points                     *)
(* |          evar | == | empirical variance                                  *)
(* |    emean_cond | == | mean of the at least $1 - \varepsilon$ fraction     *)
(* |               |    | (under c) of remaining good points                  *)
(* |     evar_cond | == |                                                     *)
(* |  filter1D_inv | == | the amount of mass removed from the good points is  *)
(* |               |    | smaller than that removed from the bad points       *)
(* | filter1D_invW | == | the amount of mass attached to the good points is   *)
(* |               |    | at least $1 - \varepsilon$                          *)
(* |      filter1D | == | robust mean estimation by comparing mean and        *)
(* |               |    | variance                                            *)
(*                                                                            *)
(******************************************************************************)

Definition is_01 (U : finType) (C : {ffun U -> R}) :=
  forall i, 0 <= C i <= 1.

Module Weighted.
Section def.
Variables (A : finType) (d0 : {fdist A}) (g : nneg_finfun A).

Definition total := \sum_(a in A) g a * d0 a.

Hypothesis total_neq0 : total != 0.

Definition f := [ffun a => g a * d0 a / total].

Lemma total_gt0 : (0 < total)%mcR.
Proof.
rewrite lt_neqAle eq_sym total_neq0/= /total sumr_ge0// => i _.
by apply/mulr_ge0/FDist.ge0; case: g => ? /= /forallP.
Qed.

Let f0 a : (0 <= f a)%mcR.
Proof.
rewrite ffunE /f coqRE divr_ge0//; last exact/ltW/total_gt0.
by rewrite coqRE mulr_ge0 //; case: g => ? /= /forallP; exact.
Qed.

Let f1 : \sum_(a in A) f a = 1.
Proof.
rewrite /f; under eq_bigr do rewrite ffunE divRE.
by rewrite -big_distrl /= mulRV.
Qed.

Definition d : {fdist A} := locked (FDist.make f0 f1).

Lemma dE a : d a = g a * d0 a / total.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.

End def.
End Weighted.

Module Split.
Section def.
Variables (A : finType) (d0 : {fdist A}) (h : nneg_finfun A).
Hypothesis weight_C : is_01 h.

Definition g := fun x => if x.2 then h x.1 else 1 - h x.1.

Definition f := [ffun x => g x * d0 x.1].

Lemma g_ge0 x : (0 <= g x)%mcR.
Proof.
rewrite /g; case: ifPn => _; first by case: h => ? /= /forallP.
by have [_ ?] := weight_C x.1; exact/RleP/subR_ge0.
Qed.

Let f0 a : (0 <= f a)%mcR.
Proof. by rewrite ffunE /f coqRE mulr_ge0 //; exact: g_ge0. Qed.

Let f1 : \sum_a f a = 1.
Proof.
transitivity (\sum_(x in ([set: A] `* setT)%SET) f x).
  by apply: eq_bigl => /= -[a b]; rewrite !inE.
rewrite big_setX/= exchange_big//= setT_bool.
rewrite big_setU1//= ?inE// big_set1//=.
rewrite -big_split//= -(Pr_setT d0).
by apply: eq_bigr => a _; rewrite !ffunE /g /=; lra.
Qed.

Definition d : {fdist _} := locked (FDist.make f0 f1).

Definition fst_RV (X : {RV d0 -> R}) : {RV d -> R} := fun x => X x.1.

Lemma dE a : d a = (if a.2 then h a.1 else (1 - h a.1)) * d0 a.1.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.

Lemma Pr_setXT good : Pr d0 good = Pr d (good `* [set: bool]).
Proof.
rewrite /Pr big_setX/=; apply: eq_bigr => u ugood.
rewrite setT_bool big_setU1//= ?inE// big_set1.
by rewrite !dE/= -mulRDl addRCA addR_opp subRR addR0 mul1R.
Qed.

Lemma cEx (X : {RV d0 -> R}) good :
  `E_[X | good] = `E_[fst_RV X | (good `* [set: bool])].
Proof.
rewrite !cExE -Pr_setXT; congr (_ / _).
rewrite big_setX//=; apply: eq_bigr => u ugood.
rewrite setT_bool big_setU1//= ?inE// big_set1.
rewrite !dE/= /fst_RV/=.
by rewrite -mulRDr -mulRDl addRCA addR_opp subRR addR0 mul1R.
Qed.

End def.
End Split.

Definition mean (U : finType) (P : {fdist U}) (X : {RV P -> R}) (A : {set U}) :=
  `E_[X | A].

Definition var (U : finType) (P : {fdist U}) (X : {RV P -> R}) (A : {set U}) :=
  `V_[X | A].

Section emean.
Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U).
Hypothesis (PC_neq0 : Weighted.total P C != 0).

Definition emean := let WP := Weighted.d PC_neq0 in
                    let WX : {RV WP -> R} := X in
                    `E WX.

Lemma emeanE :
  emean = (\sum_(i in U) C i * P i * X i) / \sum_(i in U) C i * P i.
Proof.
rewrite /emean /Ex /ambient_dist divRE big_distrl/=; apply: eq_bigr => u _.
rewrite -mulRA mulRCA; congr (_ * _).
by rewrite Weighted.dE (mulRC _ (P u)) -divRE; congr (_ / _).
Qed.

Lemma emean0 : (forall u, X u = 0) -> emean = 0.
Proof.
move=> X0.
rewrite emeanE.
under eq_bigr do rewrite X0 mulR0.
by rewrite big1 // divRE mul0R.
Qed.

End emean.

Section sq_dev.
Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U).
Hypothesis (PC_neq0 : Weighted.total P C != 0).

Definition sq_dev := let mu_hat := emean X PC_neq0 in
                     (X `-cst mu_hat)`^2.

Lemma sq_devE : sq_dev = (X `-cst (emean X PC_neq0))`^2.
Proof. by []. Qed.

Lemma sq_dev_ge0 u : 0 <= sq_dev u.
Proof. by rewrite /sq_dev sq_RV_pow2; exact: pow2_ge_0. Qed.

Definition sq_dev_max := \rmax_(i | C i != 0) sq_dev i.

Lemma Weighted_support_nonempty : {i | C i != 0}.
Proof.
move: PC_neq0; rewrite psumr_neq0; last first.
  by move=> *; apply: mulr_ge0 => //; exact: nneg_finfun_ge0.
case/hasP/sig2W=> /= x ?.
move/RltP/pmulR_lgt0'.
have:= fdist_ge0_le1 P x.
case/andP=> /[swap] _ /RleP /[swap] /[apply].
move/ltR_eqF; rewrite eq_sym => ?.
by exists x.
Qed.

Local Notation j := (sval Weighted_support_nonempty).

Definition sq_dev_arg_max :=
  [arg max_(i > j | C i != 0) sq_dev i]%O.

Lemma sq_dev_max_eq_arg :
  sq_dev_max = sq_dev (sq_dev_arg_max).
Proof.
rewrite /sq_dev_max bigmaxRE.
apply: bigmax_eq_arg; first by case: Weighted_support_nonempty.
move=> *; exact/RleP/sq_dev_ge0.
Qed.

Lemma sq_dev_max_ge0 : 0 <= sq_dev_max.
Proof.
by rewrite /sq_dev_max -big_filter; apply bigmaxR_ge0=> *; exact: sq_dev_ge0.
Qed.

Lemma sq_dev_max_ge u : C u != 0 -> sq_dev u <= sq_dev_max.
Proof.
move=> Cu0.
rewrite /sq_dev_max -big_filter; apply: leR_bigmaxR.
by rewrite mem_filter Cu0 mem_index_enum.
Qed.

End sq_dev.

Section evar.
Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U).
Hypothesis (PC_neq0 : Weighted.total P C != 0).

Definition evar := let WP := Weighted.d PC_neq0 in
                   let WX : {RV WP -> R} := X in
                   `V WX.

Lemma evarE : evar = emean (sq_dev X PC_neq0) PC_neq0.
Proof. by []. Qed.
(*Lemma evarE' : evar = emean ((X `-cst emean X PC_neq0) `^2) PC_neq0.
Proof. by []. Qed.*)

Lemma evar0P : reflect (forall i, C i * P i * sq_dev X PC_neq0 i = 0) (evar == 0).
Proof.
rewrite evarE emeanE.
apply: (iffP idP); last first.
  move=> H; under eq_bigr do rewrite H.
  by rewrite big1 // div0R.
rewrite mulR_eq0' => /orP []; last first.
  by move/invR_eq0'; have:= PC_neq0; rewrite /Weighted.total => /negPf ->.
move/[swap] => i.
rewrite psumr_eq0.
  by move/allP/(_ i)/[!mem_index_enum]/(_ erefl)/implyP/[!inE]/(_ erefl)/eqP->.
move=> x _; apply/RleP/mulR_ge0; last exact: sq_dev_ge0.
by apply/mulR_ge0=> //; exact/RleP/nneg_finfun_ge0.
Qed.

Lemma evar_ge0 : 0 <= evar.
Proof.
rewrite evarE emeanE; apply: mulR_ge0; last first.
  exact/invR_ge0/RltP/Weighted.total_gt0.
have->: 0 = \sum_(i in U) 0 by rewrite big1.
apply: leR_sumR=> i iU.
apply: mulR_ge0; last exact: sq_dev_ge0.
by apply: mulR_ge0 => //; exact/RleP/nneg_finfun_ge0.
Qed.

End evar.

Section pos_evar.
Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U).
Hypotheses (PC_neq0 : Weighted.total P C != 0) (evar_gt0 : 0 < evar X PC_neq0).

Lemma pos_evar_index :
  exists i, 0 < C i * P i * sq_dev X PC_neq0 i.
Proof.
move: evar_gt0; rewrite ltR_neqAle => -[] /nesym /eqP /[swap] _.
case/evar0P/boolp.existsNP=> x /eqP ?; exists x.
rewrite ltR_neqAle; split; first exact/nesym/eqP.
apply: mulR_ge0; last exact/sq_dev_ge0.
apply: mulR_ge0=> //; exact/RleP/nneg_finfun_ge0.
Qed.
End pos_evar.

Definition emean_cond (U : finType) (P : {fdist U}) (X : {RV P -> R})
    (C : nneg_finfun U) (A : {set U}) (PC_neq0 : Weighted.total P C != 0) :=
  let WP := Weighted.d PC_neq0 in
  let WX : {RV WP -> R} := X in
  `E_[WX | A].

Definition evar_cond (U : finType) (P : {fdist U}) (X : {RV P -> R})
    (C : nneg_finfun U) (A : {set U}) (PC_neq0 : Weighted.total P C != 0) :=
  let WP := Weighted.d PC_neq0 in
  let WX : {RV WP -> R} := X in
  `V_[WX | A].

(**md ## eqn I, page 5 *)
Definition filter1D_inv (U : finType) (P : {fdist U}) (C : nneg_finfun U)
    (good : {set U}) (eps : R) :=
  \sum_(i in good) (1 - C i) * P i <=
  (1 - eps) / 2 * \sum_(i in ~: good) (1 - C i) * P i.

(**md ## page 62, line -1 *)
Definition filter1D_invW (U : finType) (P : {fdist U}) (C : nneg_finfun U)
    (good : {set U}) (eps : R) (PC_neq0 : Weighted.total P C != 0) :=
  let WP := Weighted.d PC_neq0 in
  1 - eps <= Pr WP good.


Section bounding_empirical_mean.
Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U)
  (good : {set U}) (eps : R).

Let bad := ~: good.
Let eps_max := 1/16.

Hypotheses (C01 : is_01 C) (PC_neq0 : Weighted.total P C != 0)
  (pr_bad : Pr P bad = eps) (low_eps : eps <= eps_max).

Let WP := Weighted.d PC_neq0.
Let SP := Split.d P C01.

Lemma pr_good : Pr P good = 1 - eps. Proof. by rewrite Pr_to_cplt pr_bad. Qed.

Let eps0 : 0 <= eps. Proof. rewrite -pr_bad. exact: Pr_ge0. Qed.

Let WX : {RV WP -> R} := X.
Let SX := Split.fst_RV C01 X.

Let mu := mean X good.
Let var := var X good.

Let mu_hat := emean X PC_neq0.
Let var_hat := evar X PC_neq0.

Let mu_wave := emean_cond X good PC_neq0.
Let evar_wave := evar_cond X good PC_neq0.

Let tau := sq_dev X PC_neq0.
Let tau_max := sq_dev_max X PC_neq0.

Lemma pr_good_gt0 : 0 < Pr P good.
Proof.
unfold eps_max in low_eps.
have : 1 - Pr P good < 1; last lra.
rewrite -Pr_of_cplt pr_bad; lra.
Qed.
Let hprgoodgt0 := pr_good_gt0.

Lemma weighted_total_gt0 : 0 < Weighted.total P C.
Proof. by apply/RltP; apply Weighted.total_gt0. Qed.
Let hweightedtotalgt0 := weighted_total_gt0.

(**md ## eqn 1.1, page 5 *)
Lemma weight_contrib :
  (\sum_(i in good) C i * P i * tau i) / Pr P good <= var + (mu - mu_hat)².
Proof.
apply (@leR_trans (`E_[tau | good]));
  last by apply/leR_eqVlt;left;apply/cVarDist.
rewrite cExE.
apply leR_pmul2r; [by apply invR_gt0|].
apply leR_sumRl => i Higood; last by [].
  rewrite (mulRC (tau i)).
  apply leR_wpmul2r; first by apply sq_dev_ge0.
  have [_ c1] := C01 i.
  have /RleP hp := FDist.ge0 P i.
  by rewrite -{2}(mul1R (P i)); apply leR_wpmul2r.
by apply mulR_ge0 => //; apply sq_dev_ge0.
Qed.

Let invariant := filter1D_inv P C good eps.
Let invariantW := filter1D_invW good eps PC_neq0.

Lemma invariant_impl : invariant -> invariantW.
Proof.
rewrite /invariant /invariantW /filter1D_invW => hinv.
rewrite -!pr_good.
apply (@leR_trans ((Pr P good / 2 *
                    (1 + Pr P good + (\sum_(i in bad) C i * P i))) /
                   (\sum_(i in U) C i * P i))).
  apply (@leR_pmul2r ((\sum_(i in U) C i * P i) * 2)); first exact: mulR_gt0.
  rewrite !mulRA !(mulRC _ 2) -(mulRA _ (/ _)) mulVR; last exact: gtR_eqF.
  rewrite mulR1 !mulRA (mulRC _ (/2)) mulRA mulVR; last exact: gtR_eqF.
  rewrite mul1R -addRR mulRDl -addRA mulRDr.
  apply: leR_add.
    apply leR_pmul2l; first by move: low_eps; rewrite pr_good /eps_max; lra.
    rewrite -(Pr_setT P) /Pr.
    apply leR_sumRl => i _ //.
    by rewrite //-{2}(mul1R (P i)); apply leR_wpmul2r; [|apply C01].
  apply leR_pmul2l; first by move: low_eps; rewrite /eps_max pr_good; lra.
  rewrite /Pr addRC -bigID2.
  apply leR_sumR => i HiU.
  case: ifPn => igood; first by apply Rle_refl.
  by rewrite -{2}(mul1R (P i)); apply leR_pmul => //;
    [apply C01|apply C01|exact: Rle_refl].
under [X in _ <= X]eq_bigr do rewrite Weighted.dE /Weighted.total.
rewrite -big_distrl/= divRE.
apply leR_pmul2r; first exact: invR_gt0.
apply Ropp_le_cancel.
rewrite {2}pr_good addRA -addRA -pr_bad mulRDr oppRD addRC.
apply leR_subl_addr.
rewrite /Rminus oppRK -mulRN addRC {1}/Rdiv -mulRA mulVR; last exact: gtR_eqF.
rewrite mulR1 oppRD oppRK !big_morph_oppR-!big_split/=.
have H : forall S, \sum_(i in S) (P i + - (C i * P i)) = \sum_(i in S) (1 - C i) * P i.
  by move => p S; apply eq_bigr => i _; rewrite mulRBl mul1R addR_opp.
by rewrite !H pr_good.
Qed.

(**md ## eqn page 63, line 3 *)
Lemma bound_emean : Pr WP good != 0 ->
  invariantW ->
  (mu_hat - mu_wave)² <= var_hat * 2 * eps / (1 - eps).
Proof.
move=> pgoodC invC.
unfold eps_max in low_eps.
suff h : `| mu_hat - mu_wave | <= sqrt (var_hat * 2 * eps / (1 - eps)).
  rewrite Rsqr_abs -[X in _ <= X]Rsqr_sqrt; last first.
    apply: mulR_ge0; last by apply/invR_ge0/subR_gt0; lra.
    by rewrite -mulRA; apply: mulR_ge0; [exact: variance_ge0|lra].
  by apply/Rsqr_incr_1 => //; [exact/normR_ge0|exact: sqrt_pos].
pose delta := 1 - eps.
have {1}-> : eps = 1 - delta by rewrite subRB subRR add0R.
rewrite -/delta distRC.
rewrite /mu_hat.
by apply: resilience => //; rewrite /delta; lra.
Qed.

(**md ## eqn page 63, line 5 *)
Lemma good_mass : invariant ->
  1 - eps/2 <= (\sum_(i in good) C i * P i) / Pr P good.
Proof.
rewrite /eps_max/is_01 => Hinv.
unfold eps_max in low_eps.
apply (@leR_trans (1 - (1 - eps) / 2 / Pr P good * Pr P bad)).
  rewrite pr_bad pr_good.
  rewrite -!mulRA mulRC (mulRC (/(_-_))) mulRA -mulRA mulVR.
    by rewrite mulR1 mulRC; right.
  by apply /gtR_eqF; lra.
apply (@leR_trans (1 - (1 - eps) / 2 / Pr P good *
                       \sum_(i in bad) P i * (1 - C i))).
  rewrite leR_add2l leR_oppl oppRK leR_pmul2l; last first.
    by rewrite pr_good /Rdiv mulRC mulRA mulVR; [lra|rewrite gt_eqF//; apply/RltP; lra].
  apply leR_sumR => i Hi_bad.
  rewrite -{2}(mulR1 (P i)).
  move: (FDist.ge0 P i); move/RleP => [HPi_gt0|HPi_eq0].
    by apply/RleP; rewrite !coqRE ler_wpM2l// gerBl//; move: (C01 i).1 => /RleP.
  by rewrite -HPi_eq0 !mul0R.
rewrite -pr_good /Rdiv -(mulRA (Pr P good)) (mulRC (/2)) mulRA mulRV; last first.
  by apply gtR_eqF; rewrite pr_good; lra.
apply (@leR_pmul2r (Pr P good)); first by rewrite pr_good; lra.
rewrite -(mulRA _ (/ Pr P good)) mulVR; last by rewrite gtR_eqF// pr_good; lra.
rewrite mul1R mulR1.
rewrite mulRDl mul1R {2}pr_good mulRC mulRN.
apply (@Rplus_le_reg_l (- Pr P good)).
rewrite addRA (addRC (- _)) addRN add0R mulRA.
apply leR_oppl.
rewrite oppRD oppRK /Pr -(mul1R (- _)) mulRN -mulNR big_distrr -big_split -divRE/=.
under eq_bigr => i _ do
  rewrite mulNR mul1R -{1}(mul1R (P i)) -mulNR -Rmult_plus_distr_r addR_opp.
under [X in _ <= _ / _ * X]eq_bigr => i _ do rewrite mulRC.
by [].
Qed.

(**md ## eqn page 63, line 4 *)
Lemma bound_mean : invariant -> (mu - mu_wave)² <= var * 2 * eps / (2 - eps).
Proof.
move=> Hinv.
unfold eps_max in low_eps.
have -> : mu = `E_[SX | good `* [set: bool]] by exact: Split.cEx.
have -> : mu_wave = `E_[SX | good `* [set true]].
  rewrite /mu_wave /emean_cond !cExE !divRE !big_distrl/= big_setX//=.
  rewrite /Pr big_setX//=; apply: eq_bigr => u ugood.
  rewrite big_set1 /WP /SP.
  rewrite /WX /SX /Split.fst_RV /=.
  rewrite -!mulRA.
  congr (X u * _).
  under [in RHS]eq_bigr do rewrite big_set1 Split.dE/=.
  rewrite Split.dE/=.
  under [in LHS]eq_bigr do rewrite Weighted.dE.
  rewrite -big_distrl/=.
  rewrite -divRE Rdiv_mult_distr divRE invRK.
  rewrite mulRC !mulRA; congr (_ * / _).
  by rewrite Weighted.dE mulRA mulRAC -divRE divRR ?mul1R.
rewrite Rsqr_neg_minus.
apply: (@leR_trans (`V_[ SX | good `* [set: bool]] * 2 *
                    (1 - (1 - eps / 2)%mcR) / (1 - eps / 2)%mcR)).
  apply: sqrt_le_0.
  - exact: Rle_0_sqr.
  - apply: mulR_ge0.
    + apply: mulR_ge0.
      * by apply: mulR_ge0; [exact: cvariance_ge0|lra].
      * by rewrite -!coqRE subRB subRR add0R; exact: divR_ge0.
    + by apply: invR_ge0; rewrite -!coqRE (_ : 2%:R = 2)//; lra.
  - rewrite sqrt_Rsqr_abs; apply: (cresilience (delta := 1 - eps / 2)).
    + by rewrite -!coqRE (_ : 2%:R = 2)//; nra.
    + have := good_mass Hinv.
      rewrite -!coqRE => /leR_trans; apply.
      apply/leR_eqVlt; left.
      rewrite /Pr !big_setX/=.
      under [X in _ = X * _]eq_bigr do rewrite big_set1.
      congr (_ / _).
        apply: eq_bigr => u ugood.
        by rewrite /SP Split.dE/= mulRC.
      apply: eq_bigr => u ugood.
      rewrite setT_bool big_setU1//= ?inE// big_set1.
      by rewrite /SP !Split.dE/= -mulRDl addRCA addR_opp subRR addR0 mul1R.
    + apply leR_sumRl => i; rewrite inE => /andP[igood _].
      * by right.
      * rewrite Split.dE; apply mulR_ge0 => //.
        by case: ifPn => _; move: (C01 i.1) => [c0 c1]//; apply subR_ge0.
      * by rewrite inE igood in_setT.
    + apply/subsetP => x.
      by rewrite !inE => /andP[->].
have -> : `V_[ SX | good `* [set: bool]] = var.
  rewrite /var /cVar.
  have -> : `E_[ SX | (good `* [set: bool])] = `E_[X | good].
    by apply/esym; exact: Split.cEx.
  by apply/esym; exact: Split.cEx.
rewrite !divRE -(mulRA _ eps) -(mulRA _ (1 - _)).
apply leR_wpmul2l.
  by apply mulR_ge0; [exact: cvariance_ge0|lra].
rewrite -!coqRE subRB subRR add0R.
rewrite -!divRE -Rdiv_mult_distr Rmult_minus_distr_l mulR1.
rewrite Rmult_div_assoc (mulRC 2) -Rmult_div_assoc divRR ?mulR1.
  by rewrite (_ : 2%:R = 2)//; exact: Rle_refl.
by apply/eqP; lra.
Qed.

(**md ## lemma 1.4, page 5 (part 1) *)
Lemma bound_mean_emean : invariant ->
  `|mu - mu_hat| <= sqrt (var * 2 * eps / (2 - eps)) +
                    sqrt (var_hat * 2 * eps / (1 - eps)).
Proof.
move=> IC.
unfold eps_max in low_eps.
have I1C : invariantW.
  apply: invariant_impl => //.
apply: (@Rle_trans _ (`|mu - mu_wave| + `|mu_hat - mu_wave|)).
  have -> : mu - mu_hat = (mu - mu_wave) + (mu_wave - mu_hat) by lra.
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)).
  apply Rplus_le_compat_l.
  by rewrite Rabs_minus_sym; exact: Rle_refl.
have ? : 0 <= eps by rewrite -pr_bad; apply Pr_ge0.
apply: leR_add.
- rewrite -(geR0_norm _ (sqrt_pos _)); apply Rsqr_le_abs_0; rewrite Rsqr_sqrt.
  + exact: bound_mean.
  + rewrite -!mulRA; apply: mulR_ge0; last by apply invR_ge0; lra.
    by apply: mulR_ge0; [exact: cvariance_ge0|lra].
- rewrite -(geR0_norm _ (sqrt_pos _)); apply Rsqr_le_abs_0; rewrite Rsqr_sqrt.
  + apply bound_emean => //.
    by rewrite /invariantW /filter1D_invW -/WP in I1C; apply/eqP; lra.
  + apply: mulR_ge0; last by apply invR_ge0; lra.
    by rewrite -mulRA; apply mulR_ge0; [exact: variance_ge0|lra].
Qed.

End bounding_empirical_mean.

(** WIP *)
Section update.
Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U).
Hypotheses (PC_neq0 : Weighted.total P C != 0).

Let tau := sq_dev X PC_neq0.
Let tau_max := sq_dev_max X PC_neq0.

Definition arg_tau_max :=
  [arg max_(i > (fdist_supp_choice P) in [set: U]) tau i]%O.

Definition update_ffun : {ffun U -> R} :=
  [ffun i => if (tau_max == 0) || (C i == 0) then 0 else
            C i * (1 - tau i / tau_max)].

Lemma update_pos_ffun : [forall a, 0 <= update_ffun a]%mcR.
Proof.
apply/forallP=> u; apply/RleP.
rewrite /update_ffun ffunE.
have [_|/=] := eqVneq tau_max 0 => //=.
move/eqP; rewrite eqR_le => /boolp.not_andP []; last first.
  by move/(_ (sq_dev_max_ge0 _ _)).
rewrite -ltRNge => tau_max_gt0.
case: ifPn=> [|Cu0]; first by move=> _.
apply mulR_ge0; first exact/RleP/nneg_finfun_ge0.
rewrite subR_ge0 leR_pdivr_mulr // mul1R.
exact: sq_dev_max_ge.
Qed.

Definition update : nneg_finfun U := mkNNFinfun update_pos_ffun.

End update.

(** part 2 of lemma 1.4 *)
Section bounding_empirical_variance.
Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U)
  (good : {set U}) (eps : R).

Let bad := ~: good.
Let eps_max := 1/16.

Hypotheses (C01 : is_01 C) (PC_neq0 : Weighted.total P C != 0)
  (pr_bad : Pr P bad = eps) (low_eps : eps <= eps_max).

Let WP := Weighted.d PC_neq0.
Let SP := Split.d P C01.

Let eps0 : 0 <= eps. Proof. rewrite -pr_bad. exact: Pr_ge0. Qed.

Let WX : {RV WP -> R} := X.
Let SX := Split.fst_RV C01 X.

Let mu := mean X good.
Let var := var X good.

Let mu_hat := emean X PC_neq0.
Let var_hat := evar X PC_neq0.

Let tau := sq_dev X PC_neq0.
Let tau_max := sq_dev_max X PC_neq0.

Let invariant := filter1D_inv P C good eps.
Let invariantW := filter1D_invW good eps PC_neq0.

(**md ## lemma 1.4, page 5 (part 2) *)
(**md ## eqn A.6--A.9, page 63 *)
Lemma bound_empirical_variance_good :
  16 * var <= var_hat ->
  invariant ->
  \sum_(i in good) C i * P i * tau i <= 0.25 * (1 - eps) * var_hat.
Proof.
rewrite /eps_max; move => var16 IC.
unfold eps_max in low_eps.
have I1C : invariantW. (* todo: repeated, factor out *)
  by apply: invariant_impl.
have Hvar_hat_2_eps: 0 <= var_hat * 2 * eps.
  by rewrite -mulRA; apply: mulR_ge0; [exact: variance_ge0|lra].
rewrite /var_hat.
have PrPgoodpos : 0 < Pr P good by move: pr_bad; rewrite Pr_of_cplt; lra.
(*a6*)
apply (@leR_trans ((1 - eps) * (var + (mu - mu_hat)²))).
  by rewrite -!(pr_good pr_bad) Rmult_comm -leR_pdivr_mulr//; apply: weight_contrib => //; rewrite pr_bad.
(*a6-a7*)
apply (@leR_trans ((1 - eps) * (var + (sqrt (var * 2 * eps / (2 - eps)) +
                                       sqrt (var_hat * 2 * eps / (1 - eps)))²))).
  apply leR_wpmul2l.
    by rewrite -pr_bad subR_ge0; exact: Pr_1.
  apply/leR_add2l/Rsqr_le_abs_1.
  rewrite [x in _ <= x]geR0_norm; first exact: bound_mean_emean.
  exact/addR_ge0/sqrt_pos/sqrt_pos.
(*a7-a8*)
apply (@leR_trans ((1 - eps) * var_hat *
                   (/16 + 2 * eps *
                          (/ (4 * sqrt (2 - eps)) + / (sqrt (1 - eps)))²))).
  rewrite -(mulRA (1 - eps)).
  apply leR_pmul2l; first lra.
  rewrite mulRDr.
  apply leR_add; first lra.
  rewrite 2!mulRA -(Rsqr_sqrt (var_hat * 2 * eps)); last exact: Hvar_hat_2_eps.
  rewrite -Rsqr_mult mulRDr.
  apply Rsqr_incr_1; last 2 first.
    by apply addR_ge0; apply sqrt_pos.
    apply: addR_ge0; apply: mulR_ge0.
    - exact: sqrt_pos.
    - by apply: invR_ge0; interval.
    - exact: sqrt_pos.
    - by apply: invR_ge0; interval.
  apply: leR_add.
    apply: (@leR_trans (sqrt (var_hat * 2 * eps * / (4 * 4 * (2 - eps))))); last first.
      rewrite sqrt_mult; [|lra|apply: invR_ge0; lra].
      rewrite sqrt_inv//.
      rewrite (sqrt_mult (4 * 4)); [|lra|lra].
      by rewrite -Rsqr_def sqrt_Rsqr; [exact: Rle_refl|lra].
    apply sqrt_le_1.
    - rewrite /Rdiv -!mulRA; apply mulR_ge0; first exact: cvariance_ge0.
      apply: mulR_ge0; first lra.
      by apply: mulR_ge0; [lra|by apply invR_ge0; lra].
    - apply mulR_ge0; first exact: Hvar_hat_2_eps.
      by [lra|left;apply invR_gt0;lra].
    - rewrite invRM; [|by apply/eqP; lra..].
      rewrite (mulRC (/ _)) mulRA (mulRC _ (/ _)) mulRA mulRA mulRA /Rdiv -4!mulRA.
      apply leR_pmul.
      + exact: cvariance_ge0.
      + apply: mulR_ge0; first lra.
        by apply: mulR_ge0 => //; apply: invR_ge0; lra.
      + by rewrite mulRC /Rsqr; by lra.
      + exact: Rle_refl.
  rewrite -sqrt_inv -sqrt_mult; [|exact: Hvar_hat_2_eps|by apply: invR_ge0; lra].
  by rewrite Rsqr_sqrt; [by right|nra].
(*a8-a9*)
apply (@leR_trans ((1 - eps) * var_hat *
                   (/16 + 2 * eps_max *
                    Rsqr (/ (4 * sqrt (2 - eps_max)) + /sqrt (1 - eps_max))))).
  apply: leR_pmul.
  - by apply mulR_ge0; [lra|exact: variance_ge0].
  - by apply addR_ge0; [lra|apply: mulR_ge0; [lra|exact: Rle_0_sqr]].
  - exact: Rle_refl.
  - apply leR_add; first exact/Rle_refl.
    apply leR_pmul; [lra|exact: Rle_0_sqr|by rewrite /eps_max; lra|].
    apply Rsqr_bounds_le; split; first by interval.
    apply leR_add.
      apply leR_inv.
      + apply mulR_gt0; first lra.
        by apply sqrt_lt_R0; rewrite /eps_max; lra.
      + apply leR_wpmul2l; first lra.
        by apply sqrt_le_1; rewrite /eps_max; lra.
    apply leR_inv.
      by apply sqrt_lt_R0; rewrite /eps_max; lra.
    by apply sqrt_le_1; rewrite /eps_max; lra.
rewrite mulRC mulRA.
apply: leR_wpmul2r => //; first exact: variance_ge0.
by apply leR_wpmul2r; [lra|rewrite /eps_max; interval].
Qed.

(**md ## eqn A.10--A.11, page 63 *)
Lemma bound_empirical_variance_bad :
  16 * var <= var_hat ->
  invariant ->
  2/3 * var_hat <= \sum_(i in bad) C i * P i * tau i.
Proof.
rewrite /eps_max; move => var16 HiC.
unfold eps_max in low_eps.
have ? : 0 < Pr P good; first exact: (pr_good_gt0 _ low_eps).

have ->: \sum_(i in bad) C i * P i * tau i =
  var_hat * (\sum_(i in U) C i * P i) - (\sum_(i in good) C i * P i * tau i).
  rewrite /var_hat /evar /Var {1}/Ex.
  apply: (Rplus_eq_reg_r (\sum_(i in good) C i * P i * tau i)).
  rewrite -addRA Rplus_opp_l addR0.
  rewrite /bad.
  have -> : \sum_(i in ~: good) C i * P i * tau i +
            \sum_(i in good) C i * P i * tau i = \sum_(i in U) C i * P i * tau i.
    rewrite -big_union/=; last first.
      by rewrite disjoints_subset setCK.
    rewrite setUC setUCr/=.
    by apply: eq_bigl => //= u; rewrite inE.
  rewrite big_distrl/=.
  apply: eq_bigr => i _.
  rewrite /tau /mu_hat /WP Weighted.dE.
  rewrite mulRC -mulRA; congr (_ * _).
  rewrite /Weighted.total -mulRA Rinv_l ?mulR1//.
  exact/eqP.
apply (@leR_trans (var_hat * (1 - 3 / 2 * eps) -
    \sum_(i in good) C i * P i * tau i)); last first.
  rewrite -!addR_opp; apply: Rplus_le_compat_r.
  apply leR_wpmul2l; first exact: variance_ge0.
  apply: (@leR_trans ((1 - eps / 2) * (1 - eps))); first nra.
  apply: leR_trans.
    move: (@good_mass _ _ _ _ _ C01 pr_bad low_eps HiC).
    move/(Rmult_le_compat_r (Pr P good) _ _ (Pr_ge0 _ good)).
    rewrite -Rmult_div_swap Rmult_div_l; last exact: Rgt_not_eq.
    by rewrite Pr_to_cplt pr_bad; exact.
  apply leR_sumRl => //i igood.
  + exact: Rle_refl.
  + by apply mulR_ge0 => //; apply (C01 _).1.
apply (@leR_trans ((1 - 3 / 2 * eps - 0.25 * (1 - eps)) * var_hat)); last first.
  rewrite mulRBl (mulRC var_hat).
  apply: leR_add; last by apply Ropp_le_contravar; exact: bound_empirical_variance_good.
  exact: Rle_refl.
apply (@leR_trans ((1 - 3 / 2 * eps_max - 0.25 * (1 - eps_max)) * var_hat)); last first.
  apply leR_wpmul2r; first exact: variance_ge0.
  by rewrite /eps_max; nra.
by rewrite/eps_max; apply leR_wpmul2r; [exact: variance_ge0|nra].
Qed.

(**md ## eqn 1.3--1.4, page 7 *)
(* TODO: improve the notation for pos_ffun (and for pos_fun) *)
Lemma update_removed_weight (S : {set U}) :
  let C' := update X PC_neq0 in
  0 < tau_max ->
  \sum_(i in S) (1 - C' i) * P i =
    (\sum_(i in S) (1 - C i) * P i) +
    1 / tau_max * (\sum_(i in S) C i * P i * tau i).
Proof.
move => C' tau_max_gt0.
have <- : \sum_(i in S) (C i - C' i) * P i=
         1 / tau_max * (\sum_(i in S) C i * P i * tau i).
  rewrite /C' /update big_distrr.
  apply eq_bigr => i _ /=.
  rewrite /update_ffun ffunE.
  have [->|Ci-] := eqVneq (C i) 0; first by rewrite orbT subRR !(mulR0,mul0R).
  rewrite orbF ifF; last by rewrite (negbTE (gtR_eqF _ _ tau_max_gt0))/=.
  rewrite /tau_max /tau.
  by field; exact/eqP/gtR_eqF.
rewrite -big_split/=.
apply eq_bigr => i HiS.
by rewrite -mulRDl addRA subRK.
Qed.

End bounding_empirical_variance.

Section update_invariant.
Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U)
  (good : {set U}) (eps : R).
Hypotheses (PC_neq0 : Weighted.total P C != 0) (C01 : is_01 C).
Let var_hat := evar X PC_neq0.
Let var := var X good.
Let tau := sq_dev X PC_neq0.
Let tau_max := sq_dev_max X PC_neq0.

Hypotheses (Pr_bad : Pr P (~: good) = eps) (low_eps : eps <= 1/16)
  (var16 : 16 * var < var_hat).

Lemma sq_dev_max_neq0 : (0 < var_hat) -> sq_dev_max X PC_neq0 != 0.
Proof.
rewrite /sq_dev_max => var_hat_gt0.
have /RltP HCgt0 := weighted_total_gt0 PC_neq0.
have HCge0 := ltW HCgt0.
move: var_hat_gt0.
rewrite /var_hat /evar /Var /sq_dev /emean /Ex=> /RltP /fsumr_gt0[i _].
rewrite Weighted.dE => /[dup] => /pmulR_lgt0' => sq_dev_gt0.
have /[apply] := pmulR_rgt0' _ (sq_RV_ge0 (X `-cst \sum_(v in U) X v * Weighted.d PC_neq0 v) i).
have /[apply] := pmulR_lgt0' _ (invR_ge0 _ (RltP _ _ HCgt0)).
have /[apply] Cigt0 := pmulR_lgt0' _ (RleP _ _ (FDist.ge0 P i)).
rewrite gt_eqF//; apply/RltP/bigmaxR_gt0; exists i; split => //.
by rewrite gt_eqF//; exact/RltP.
apply/sq_dev_gt0/mulR_ge0; first by apply/mulR_ge0 => //; apply (C01 _).1.
exact/invR_ge0/weighted_total_gt0.
Qed.

(**md ## lemma 1.5, page 5, update preserves the invariant of filter1D *)
Lemma filter1D_inv_update : let C' := update X PC_neq0 in
  filter1D_inv P C good eps -> filter1D_inv P C' good eps.
Proof.
rewrite /filter1D_inv => inv.
have var_ge0 : 0 <= var by exact: cvariance_ge0.
have tau_max_gt0 : 0 < sq_dev_max X PC_neq0.
  apply ltR_neqAle; split.
    by apply/eqP; rewrite eq_sym sq_dev_max_neq0//; lra.
  rewrite /sq_dev_max.
  by apply: bigmaxR_ge0_cond => r _; apply sq_dev_ge0.
suff H2 : \sum_(i in good) (C i * P i) * tau i <=
    (1 - eps) / 2 * (\sum_(i in ~: good) (C i * P i) * tau i).
  rewrite !update_removed_weight// !mulRDr; apply leR_add; first exact inv.
  by rewrite mulRCA; apply leR_pmul2l; [exact/divR_gt0|exact: H2].
have var16' : 16 * var <= var_hat by lra.
apply: leR_trans.
  exact: (bound_empirical_variance_good C01 Pr_bad).
apply: (Rmult_le_reg_l (/((1-eps)/2))).
  by apply: invR_gt0; apply: divR_gt0 => //; lra.
rewrite mulRA mulRA mulRA Rinv_l; last by apply mulR_neq0; lra.
rewrite mul1R Rinv_div.
have -> : 2 / (1 - eps) * 0.25 * (1 - eps) = 0.5 * ((1-eps) / (1-eps)) by lra.
rewrite divRR ?mulR1; last by rewrite gt_eqF//; apply/RltP; lra.
apply: leR_trans; last first.
  exact: (bound_empirical_variance_bad C01 Pr_bad).
by apply: leR_wpmul2r; [exact: variance_ge0|lra].
Qed.

Lemma update_01 :
  is_01 (update X PC_neq0).
Proof.
move=> u; rewrite /update/=; split.
  apply/RleP.
  have /forallP := update_pos_ffun X PC_neq0.
  exact.
rewrite /update_ffun ffunE; case: ifPn => //.
rewrite negb_or => /andP[sq_dev_neq0 Cu_neq0].
move=> [:sq_gt0].
apply/RleP/mulr_ile1.
- exact/RleP/(C01 u).1.
- apply/RleP; rewrite subR_ge0 leR_pdivr_mulr// ?mul1R//; last first.
    abstract: sq_gt0.
    by apply/ltR_neqAle; split; [exact/nesym/eqP|exact/sq_dev_max_ge0].
  exact: sq_dev_max_ge.
- exact/RleP/(C01 u).2.
- apply/RleP; rewrite leR_subl_addr addRC -leR_subl_addr subRR.
  by apply/divR_ge0 => //; exact: sq_dev_ge0.
Qed.

End update_invariant.

Section base_case.
(* TODO: define a proper environment *)
Variables (A : finType) (P : {fdist A}) (eps : R) (good : {set A}).

Definition ffun1 : {ffun A -> R} := [ffun=> 1].
Let ffun1_subproof : [forall a, 0 <= ffun1 a]%mcR.
Proof. by apply/forallP => u; rewrite ffunE; apply/RleP. Qed.
Definition Cpos_ffun1 := @mkNNFinfun A ffun1 ffun1_subproof.

Lemma PC1_neq0 : Weighted.total P Cpos_ffun1  != 0.
Proof.
rewrite/Weighted.total.
under eq_bigr => i _ do rewrite /Cpos_ffun1/=/ffun1 ffunE mul1R.
rewrite FDist.f1.
apply oner_neq0.
Qed.

Lemma C1_is01 : is_01 Cpos_ffun1.
Proof. by move => i; rewrite ffunE; lra. Qed.

Lemma base_case: Pr P (~: good) = eps ->
  filter1D_inv P Cpos_ffun1 good eps.
Proof.
move=> Hbad_ratio; rewrite /filter1D_inv.
rewrite /Cpos_fun /=.
under eq_bigr do rewrite ffunE subRR mul0R.
rewrite big1; last by [].
under eq_bigr do rewrite ffunE subRR mul0R.
rewrite big1; last by [].
by rewrite mulR0; exact/RleP.
Qed.

End base_case.

Require Import FunInd Recdef.

Notation "a '<=?' b" := (Bool.bool_dec (Rleb a b) true).
Notation "a '!=?' b" := (Bool.bool_dec (a != b) true) (at level 70).

(**md ## Algorithm 2, page 4 *)
Section real_filter1D.
Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}).

Local Obligation Tactic := idtac.

Lemma tr x y : Rleb x y <> true -> y < x.
Proof. by move=> /negP/RlebP/RleP; rewrite -ltNge => /RltP. Qed.

Lemma filter1D_arg_decreasing (C : nneg_finfun U) (var : R) :
  0 <= var -> is_01 C ->
  forall HC : Weighted.total P C != 0,
  forall K : Rleb (evar X HC) (16 * var) <> true,
  (#|0.-support (update X HC)| < #|0.-support C|)%coq_nat.
Proof.
rewrite/Weighted.total=> var_ge0 C01 HCneq0 evar16.
apply/ssrnat.ltP/proper_card/properP; split.
  apply/subsetP => u; rewrite !supportE /update_ffun ffunE.
  by case: ifPn; [rewrite eqxx|rewrite negb_or => /andP[]].
have /RltP HCgt0 := weighted_total_gt0 HCneq0.
have HCge0 := ltW HCgt0.
move: (HCgt0) => /fsumr_gt0[u _ /RltP].
rewrite mulr_ge0_gt0// => [/andP[Cu0 Pu0]|]; last by apply/RleP; exact: (C01 u).1.
have Cmax_neq0 : C [arg max_(i > u | C i != 0) sq_dev X HCneq0 i]%O != 0.
  by case: arg_maxP => //; rewrite gt_eqF.
have sq_dev_max_neq0 : sq_dev_max X HCneq0 != 0.
  apply: sq_dev_max_neq0 => //; apply: (Rle_lt_trans 0); last apply (tr evar16); apply mulR_ge0; [lra|apply var_ge0].
exists [arg max_(i > u | C i != 0) sq_dev X HCneq0 i]%O.
  by rewrite supportE.
rewrite /update_ffun supportE ffunE negbK ifF.
  rewrite !coqRE mulf_eq0 subr_eq0 -invr1 -(mul1r (1^-1))%mcR.
  rewrite eqr_div ?oner_eq0// ?mulr1 ?mul1r// /sq_dev_max bigmaxRE.
  rewrite (@bigmax_eq_arg _ _ _ _ u) ?eq_refl ?orbT ?gt_eqF//.
  by move=> i _; exact/RleP/sq_dev_ge0.
by rewrite (negbTE sq_dev_max_neq0)/=; exact/negbTE.
Qed.

Function real_filter1D_rec (var : R) (var_ge0: 0 <= var)
  (C : nneg_finfun U) (C01 : is_01 C) (HC : Weighted.total P C != 0)
  {measure (fun C => #| 0.-support C |) C} :=
  let empirical_mean := emean X HC in
  let empirical_variance := evar X HC in
  match empirical_variance <=? 16 * var with
  | left _ => Some empirical_mean
  | right _ =>
    let C' := update X HC in
    match Weighted.total P C' !=? 0 with
    | right _ => None
    | left H => 
        let C'01 := update_01 X HC C01 in
        @real_filter1D_rec var var_ge0 C' C'01 H
    end
  end.
Proof.
rewrite/Weighted.total=> var var_ge0 C C01 HC evar16 h2 h3 _.
apply (filter1D_arg_decreasing (var_ge0)) => //.
Qed.

Definition real_filter1D var var_ge0 := (@real_filter1D_rec var var_ge0 (Cpos_ffun1 U) (@C1_is01 U) (@PC1_neq0 _ _)).

Functional Scheme real_filter1D_rec_ind := Induction for real_filter1D_rec Sort Prop.

Lemma real_filter1D_correct good eps :
  Pr P (~: good) = eps -> eps <= 1/16 ->
  let mu := mean X good in
  let var := var X good in
  let var_ge0 := cvariance_ge0 X good in
  if real_filter1D var_ge0 is Some mu_hat
  then
    `| mu_hat - mu | <= sqrt (var * (2 * eps) / (2 - eps)) +
                       sqrt (16 * var * (2 * eps) / (1 - eps))
  else
    false.
Proof.
rewrite /real_filter1D => Pr_bad low_eps.
have := base_case Pr_bad.
apply real_filter1D_rec_ind => //=.
- move=> C C01 HC evar16 _ Inv.
  rewrite distRC.
  apply: leR_trans.
    by apply bound_mean_emean => //; rewrite Pr_bad//.
  apply leR_add.
    by rewrite /var Pr_bad mulRA; right.
  apply sqrt_le_1_alt.
  rewrite Pr_bad mulRA.
  repeat apply leR_wpmul2r.
  + by apply invR_ge0; apply subR_gt0; lra.
  + by rewrite -Pr_bad; apply Pr_ge0.
  + lra.
  by rewrite /var/weightedmean.var; apply /RleP.
- move=> C C01 HC evar16 _ PC_eq0 _ Inv.
  have PC0 : forall x, update X HC x * P x = 0.
    move: PC_eq0=> /negP/negbNE; rewrite psumr_eq0; last by move=> i _; rewrite !coqRE mulr_ge0 ?nneg_finfun_ge0.
    by move/allP=> PC0 x; apply/eqP/PC0/mem_index_enum.
  have /= := filter1D_inv_update C01 Pr_bad low_eps (tr evar16) Inv.
  rewrite /filter1D_inv.
  under eq_bigr => i ? do rewrite Rmult_plus_distr_r mulNR PC0 addR_opp subR0 mul1R.
  under [X in _ * X]eq_bigr => i _ do rewrite Rmult_plus_distr_r mulNR PC0 addR_opp subR0 mul1R.
  have -> : \sum_(i in good) P i = Pr P good by [].
  have -> : \sum_(i in ~: good) P i = Pr P (~: good) by [].
  have -> : Pr P good = 1-eps by rewrite Pr_to_cplt Pr_bad.
  nra.
- move=> C C01 HC evar16 _ PC_neq0 _ IH Inv.
  apply: IH.
  apply: filter1D_inv_update => //.
  exact: tr.
Qed.

End real_filter1D.
