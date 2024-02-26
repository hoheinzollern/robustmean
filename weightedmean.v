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
(* |    Weighted.d | == | given a distribution $d0$ and a non-negative        *)
(* |               |    | function $g$, returns the distribution              *)
(* |               |    | $a\mapsto \frac{g(a) * d0(a)}{\sum_b g(b) * d0(b)}$ *)
(* |       Split.d | == | given a distribution $d0$ and a non-negative        *)
(* |               |    | function $h$, returns the distribution              *)
(* |               |    | $\begin{array}{rl} (a,b) \mapsto & h(a) * d0(a) \textrm{ if } b \\ & (1 - h(a))*d0(a) \textrm{ o.w.}\end{array}$ *)
(* |      sq_dev X | == | "squared deviation": $(X - mean)^2$                 *)
(* |    emean_cond | == | mean of the at least $1 - \varepsilon$ fraction     *)
(* |               |    | (under c) of remaining good points                  *)
(* |         emean | == | empirical/estimate mean of the data,                *)
(* |               |    | weighted mean of all the points                     *)
(* |               |    | (defined using emean_cond)                          *)
(* |     evar_cond | == | `V_[X : {RV (Weighted.d PC0) -> R} | A]             *)
(* |          evar | == | empirical variance                                  *)
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

Lemma support_nonempty :  {i | g i != 0}.
Proof.
move: total_neq0; rewrite psumr_neq0; last first.
  by move=> *; apply: mulr_ge0 => //; exact: nneg_finfun_ge0.
case/hasP/sig2W=> /= x ?.
move/RltP/pmulR_lgt0'.
have := fdist_ge0_le1 d0 x.
case/andP=> /[swap] _ /RleP /[swap] /[apply].
by move/ltR_eqF; rewrite eq_sym => ?; exists x.
Qed.

End def.
End Weighted.

Module Split.
Section def.
Variables (T : finType) (d0 : {fdist T}) (h : nneg_finfun T).
Hypothesis h01 : is_01 h.

Definition g := fun x => if x.2 then h x.1 else 1 - h x.1.

Definition f := [ffun x => g x * d0 x.1].

Lemma g_ge0 x : (0 <= g x)%mcR.
Proof.
rewrite /g; case: ifPn => _; first by case: h => ? /= /forallP.
by have [_ ?] := h01 x.1; exact/RleP/subR_ge0.
Qed.

Let f0 a : (0 <= f a)%mcR.
Proof. by rewrite ffunE /f coqRE mulr_ge0 //; exact: g_ge0. Qed.

Let f1 : \sum_a f a = 1.
Proof.
transitivity (\sum_(x in ([set: T] `* setT)%SET) f x).
  by apply: eq_bigl => /= -[a b]; rewrite !inE.
rewrite big_setX/= exchange_big//= setT_bool.
rewrite big_setU1//= ?inE// big_set1//=.
rewrite -big_split//= -(Pr_setT d0).
by apply: eq_bigr => a _; rewrite !ffunE /g /=; lra.
Qed.

Definition d : {fdist T * bool} := locked (FDist.make f0 f1).

Definition fst_RV (X : {RV d0 -> R}) : {RV d -> R} := X \o fst.

Lemma dE a : d a = (if a.2 then h a.1 else 1 - h a.1) * d0 a.1.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.

Lemma Pr_setXT A : Pr d0 A = Pr d (A `* [set: bool]).
Proof.
rewrite /Pr big_setX/=; apply: eq_bigr => u ugood.
rewrite setT_bool big_setU1//= ?inE// big_set1.
by rewrite !dE/= -mulRDl addRCA addR_opp subRR addR0 mul1R.
Qed.

Lemma cEx (X : {RV d0 -> R}) A :
  `E_[X | A] = `E_[fst_RV X | A `* [set: bool]].
Proof.
rewrite !cExE -Pr_setXT; congr (_ / _).
rewrite big_setX//=; apply: eq_bigr => u ugood.
rewrite setT_bool big_setU1//= ?inE// big_set1.
rewrite !dE/= /fst_RV/=.
by rewrite -mulRDr -mulRDl addRCA addR_opp subRR addR0 mul1R.
Qed.

Lemma cVar (X : {RV d0 -> R}) A :
  `V_[ fst_RV X | A `* [set: bool]] = `V_[X | A].
Proof.
by rewrite /cVar/= cEx -[in LHS]cEx.
Qed.

End def.
End Split.

Section emean_cond.
Context {U : finType} (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U)
  (A : {set U}) (PC0 : Weighted.total P C != 0).

Let WP := Weighted.d PC0.
Definition emean_cond := `E_[X : {RV WP -> R} | A].

Hypothesis C01 : is_01 C.

Lemma emean_condE : let SX := Split.fst_RV C01 X in
  emean_cond = `E_[SX | A `* [set true]].
Proof.
rewrite /emean_cond !cExE !divRE !big_distrl/= big_setX//=.
rewrite /Pr big_setX//=; apply: eq_bigr => u ugood.
rewrite big_set1 /SP /Split.fst_RV /= -!mulRA; congr (X u * _).
under [in RHS]eq_bigr do rewrite big_set1 Split.dE/=.
rewrite Split.dE/=.
under [in LHS]eq_bigr do rewrite Weighted.dE.
rewrite -big_distrl/= -divRE Rdiv_mult_distr divRE invRK.
rewrite mulRC !mulRA; congr (_ * / _).
by rewrite Weighted.dE mulRA mulRAC -divRE divRR ?mul1R.
Qed.

End emean_cond.

Section emean.
Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U)
  (PC0 : Weighted.total P C != 0).

Definition emean := emean_cond X setT PC0.

(** emean expressed using expectation *)
Lemma emeanE : emean = `E (X : {RV (Weighted.d PC0) -> R}).
Proof. by rewrite /emean /emean_cond -Ex_cExT. Qed.

(** emean expressed using big sums *)
Lemma emean_sum :
  emean = (\sum_(i in U) C i * P i * X i) / \sum_(i in U) C i * P i.
Proof.
rewrite emeanE/= /Ex [in RHS]divRE big_distrl/=.
by under eq_bigr do rewrite Weighted.dE mulRCA mulRA.
Qed.

End emean.

Section sq_dev.
Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U)
  (PC0 : Weighted.total P C != 0).

Definition sq_dev := (X `-cst emean X PC0)`^2.

Lemma sq_devE : sq_dev = (X `-cst `E (X : {RV (Weighted.d PC0) -> R})) `^2.
Proof. by rewrite /sq_dev emeanE. Qed.

Lemma sq_dev_ge0 u : 0 <= sq_dev u.
Proof. by rewrite /sq_dev sq_RV_pow2; exact: pow2_ge_0. Qed.

Definition sq_dev_max := \rmax_(i | C i != 0) sq_dev i.

Local Notation j := (sval (Weighted.support_nonempty PC0)).

Definition sq_dev_arg_max := [arg max_(i > j | C i != 0) sq_dev i]%O.

Lemma sq_dev_max_eq_arg : sq_dev_max = sq_dev (sq_dev_arg_max).
Proof.
rewrite /sq_dev_max bigmaxRE.
apply: bigmax_eq_arg; first by case: Weighted.support_nonempty.
by move=> *; exact/RleP/sq_dev_ge0.
Qed.

Lemma sq_dev_max_ge0 : 0 <= sq_dev_max.
Proof.
by rewrite /sq_dev_max -big_filter; apply bigmaxR_ge0 => *; exact: sq_dev_ge0.
Qed.

Lemma sq_dev_max_ge u : C u != 0 -> sq_dev u <= sq_dev_max.
Proof.
move=> Cu0.
rewrite /sq_dev_max -big_filter; apply: leR_bigmaxR.
by rewrite mem_filter Cu0 mem_index_enum.
Qed.

End sq_dev.

Section evar_cond.
Context (U : finType) (P : {fdist U}) (X : {RV P -> R})
  (C : nneg_finfun U) (A : {set U}) (PC0 : Weighted.total P C != 0).

Let WP := Weighted.d PC0.

Definition evar_cond := `V_[X : {RV WP -> R} | A].

Lemma evar_cond_ge0 : 0 <= evar_cond. Proof. exact: cvariance_ge0. Qed.

End evar_cond.

Section evar.
Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U)
  (PC0 : Weighted.total P C != 0).

Definition evar := evar_cond X setT PC0.

Lemma evarE : evar = `V (X : {RV (Weighted.d PC0) -> R}).
Proof. by rewrite /evar /evar_cond Var_cVarT. Qed.

Lemma evar_emean : evar = emean (sq_dev X PC0) PC0.
Proof.
rewrite /evar /emean /evar_cond /emean_cond /sq_dev.
by rewrite emeanE/= -Var_cVarT -Ex_cExT.
Qed.

Lemma evar0P :
  reflect (forall i, C i * P i * sq_dev X PC0 i = 0) (evar == 0).
Proof.
apply: (iffP idP); last first.
  rewrite evar_emean emean_sum.
  move=> H; under eq_bigr do rewrite H.
  by rewrite big1 // div0R.
rewrite evar_emean emean_sum.
rewrite mulR_eq0' => /orP []; last first.
  by move/invR_eq0'; rewrite -/(Weighted.total _ _) (negbTE PC0).
move/[swap] => i.
rewrite psumr_eq0.
  by move/allP/(_ i)/[!mem_index_enum]/(_ erefl)/implyP/[!inE]/(_ erefl)/eqP->.
move=> x _; apply/RleP/mulR_ge0; last exact: sq_dev_ge0.
by apply/mulR_ge0=> //; exact/RleP/nneg_finfun_ge0.
Qed.

Lemma evar_ge0 : 0 <= evar. Proof. exact: evar_cond_ge0. Qed.

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

Hypotheses (C01 : is_01 C) (PC0 : Weighted.total P C != 0)
  (pr_bad : Pr P bad = eps) (low_eps : eps <= 1 / 16).

Lemma pr_good : Pr P good = 1 - eps. Proof. by rewrite Pr_to_cplt pr_bad. Qed.

Let eps0 : 0 <= eps. Proof. rewrite -pr_bad. exact: Pr_ge0. Qed.

Let mu := `E_[X | good].
Let var := `V_[X | good].

Let mu_hat := emean X PC0.
Let var_hat := evar X PC0.

Let mu_wave := emean_cond X good PC0.
Let evar_wave := evar_cond X good PC0.

Let tau := sq_dev X PC0.
Let tau_max := sq_dev_max X PC0.

Lemma pr_good_gt0 : 0 < Pr P good.
Proof. by rewrite pr_good; lra. Qed.
Let hprgoodgt0 := pr_good_gt0.

Lemma weighted_total_gt0 : 0 < Weighted.total P C.
Proof. by apply/RltP/Weighted.total_gt0. Qed.
Let hweightedtotalgt0 := weighted_total_gt0.

(**md ## eqn 1.1, page 5 *)
Lemma weight_contrib :
  (\sum_(i in good) C i * P i * tau i) / Pr P good <= var + (mu - mu_hat)².
Proof.
rewrite -(_ : `E_[tau | good] = _+_); [rewrite cExE|exact: cVarDist].
apply leR_pmul2r; first by apply invR_gt0.
apply leR_sumRl => i Higood //.
rewrite mulRAC -mulRA -{2}(mul1R (tau i * _)).
apply: (leR_wpmul2r _ ((C01 i).2)).
all: apply/mulR_ge0 => //; apply sq_dev_ge0.
Qed.

Let invariant := filter1D_inv P C good eps.
Let invariantW := filter1D_invW good eps PC0.

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
    apply leR_pmul2l; first by move: low_eps; rewrite pr_good; lra.
    rewrite -(Pr_setT P); apply leR_sumRl => i _ //.
    by rewrite -{2}(mul1R (P i)); apply: (leR_wpmul2r _ ((C01 i).2)).
  apply leR_pmul2l; first by move: low_eps; rewrite pr_good; lra.
  rewrite addRC -bigID2; apply leR_sumR => i HiU.
  case: ifPn => igood; first by apply Rle_refl.
  by rewrite -{2}(mul1R (P i)); apply: (leR_wpmul2r _ ((C01 i).2)).
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

Let WP := Weighted.d PC0.

(**md ## eqn page 63, line 3 *)
Lemma bound_emean : Pr WP good != 0 ->
  invariantW ->
  (mu_hat - mu_wave)² <= var_hat * 2 * eps / (1 - eps).
Proof.
move=> pgoodC invC.
suff h : `| mu_hat - mu_wave | <= sqrt (var_hat * 2 * eps / (1 - eps)).
  rewrite Rsqr_abs -[X in _ <= X]Rsqr_sqrt; last first.
    apply: mulR_ge0; last by apply/invR_ge0/subR_gt0; lra.
    by rewrite -mulRA; apply: mulR_ge0; [exact: evar_ge0|lra].
  by apply/Rsqr_incr_1 => //; [exact/normR_ge0|exact: sqrt_pos].
rewrite distRC {1}(_ : eps = 1 - (1 - eps)); last by lra.
set delta := 1 - eps.
rewrite /mu_hat emeanE /var_hat evarE.
by apply: resilience => //; rewrite /delta; lra.
Qed.

(**md ## eqn page 63, line 5 *)
Lemma good_mass : invariant ->
  1 - eps/2 <= (\sum_(i in good) C i * P i) / Pr P good.
Proof.
rewrite /is_01 => Hinv.
apply (@leR_trans (1 - (1 - eps) / 2 / Pr P good * Pr P bad)).
  rewrite pr_bad pr_good.
  rewrite -!mulRA mulRC (mulRC (/(_ - _))) mulRA -mulRA mulVR.
    by rewrite mulR1 mulRC; right.
  by apply/gtR_eqF; lra.
apply (@leR_trans (1 - (1 - eps) / 2 / Pr P good *
                       \sum_(i in bad) P i * (1 - C i))).
  rewrite leR_add2l leR_oppl oppRK leR_pmul2l; last first.
    by apply/divR_gt0 => //; apply/divR_gt0 => //; lra.
  apply leR_sumR => i ibad.
  rewrite mulRBr mulR1 leR_sub_addr leR_addl; apply: mulR_ge0 => //.
  exact: (C01 i).1.
rewrite -pr_good -mulRA mulRCA !mulRA mulVR ?mul1R; last exact/gtR_eqF.
apply/leR_pdivl_mulr => //.
rewrite mulRDl mul1R {2}pr_good mulRC mulRN.
rewrite addRC; apply/leR_subr_addr; rewrite leR_oppl oppRD oppRK addRC mulRA.
rewrite /Pr -(mul1R (- _)) mulRN -mulNR big_distrr -big_split -divRE/=.
under eq_bigr => i _ do
  rewrite mulN1R -{1}(mul1R (P i)) -mulNR -Rmult_plus_distr_r addR_opp.
by under [X in _ <= _ / _ * X]eq_bigr => i _ do rewrite mulRC.
Qed.

Let SX := Split.fst_RV C01 X.

(**md ## eqn page 63, line 4 *)
Lemma bound_mean : invariant -> (mu - mu_wave)² <= var * 2 * eps / (2 - eps).
Proof.
move=> Hinv.
have -> : mu = `E_[SX | good `* [set: bool]] by rewrite -Split.cEx.
have -> : mu_wave = `E_[SX | good `* [set true]].
  by rewrite /mu_wave emean_condE.
rewrite Rsqr_neg_minus.
apply: (@leR_trans (`V_[ SX | good `* [set: bool]] *
                    2 * (1 - (1 - eps / 2)%mcR) / (1 - eps / 2)%mcR)).
  apply: sqrt_le_0; first exact: Rle_0_sqr.
  - apply: mulR_ge0.
    + apply: mulR_ge0.
      * by apply: mulR_ge0; [exact: cvariance_ge0|lra].
      * by rewrite -!coqRE subRB subRR add0R; exact: divR_ge0.
    + by apply: invR_ge0; rewrite -!coqRE (_ : 2%:R = 2)//; lra.
  - rewrite sqrt_Rsqr_abs; apply: (cresilience (delta := 1 - eps / 2)).
    + by rewrite -!coqRE (_ : 2%:R = 2)//; lra.
    + have := good_mass Hinv.
      rewrite -Split.Pr_setXT {2}/Pr big_setX/= -!coqRE => /leR_trans; apply.
      apply/leR_eqVlt; left; congr (_ / _); apply: eq_bigr => u ugood.
      by rewrite big_set1 Split.dE.
    + by apply/subsetP => x; rewrite !inE => /andP[->].
rewrite Split.cVar !divRE -/var -(mulRA _ eps) -(mulRA _ (1 - _)).
apply: leR_wpmul2l.
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
have I1C : invariantW by exact: invariant_impl.
apply: (@Rle_trans _ (`|mu - mu_wave| + `|mu_hat - mu_wave|)).
  have -> : mu - mu_hat = (mu - mu_wave) + (mu_wave - mu_hat) by lra.
  apply/(Rle_trans _ _ _ (Rabs_triang _ _))/Rplus_le_compat_l.
  by rewrite Rabs_minus_sym; exact: Rle_refl.
have ? : 0 <= eps by rewrite -pr_bad; apply Pr_ge0.
apply: leR_add.
- rewrite -(geR0_norm _ (sqrt_pos _)); apply Rsqr_le_abs_0; rewrite Rsqr_sqrt.
  + exact: bound_mean.
  + rewrite -!mulRA; apply/mulR_ge0; last by apply invR_ge0; lra.
    by apply: mulR_ge0; [exact: cvariance_ge0|lra].
- rewrite -(geR0_norm _ (sqrt_pos _)); apply Rsqr_le_abs_0; rewrite Rsqr_sqrt.
  + apply: bound_emean => //.
    by rewrite /invariantW /filter1D_invW -/WP in I1C; apply/eqP; lra.
  + apply: mulR_ge0; last by apply invR_ge0; lra.
    by rewrite -mulRA; apply mulR_ge0; [exact: evar_ge0|lra].
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
apply/forallP=> i; apply/RleP.
rewrite /update_ffun ffunE.
case: ifPn => [/orP[//=|//]|/norP[tau_max_neq0 Ci_neq0]].
apply /mulR_ge0/RleP; first exact/RleP/nneg_finfun_ge0.
rewrite subr_ge0 coqRE ler_pdivr_mulr ?mul1r; first exact/RleP/sq_dev_max_ge.
by rewrite lt_neqAle eq_sym tau_max_neq0/=; exact/RleP/sq_dev_max_ge0.
Qed.

Definition update : nneg_finfun U := mkNNFinfun update_pos_ffun.

End update.

(** part 2 of lemma 1.4 *)
Section bounding_empirical_variance.
Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U)
  (good : {set U}) (eps : R).

Let bad := ~: good.

Hypotheses (C01 : is_01 C) (PC_neq0 : Weighted.total P C != 0)
  (pr_bad : Pr P bad = eps) (low_eps : eps <= 1/16).

Let WP := Weighted.d PC_neq0.

Let eps0 : 0 <= eps. Proof. rewrite -pr_bad. exact: Pr_ge0. Qed.

Let mu := `E_[X | good].
Let var := `V_[X | good].

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
move => var16 IC.
have I1C : invariantW. (* todo: repeated, factor out *)
  by apply: invariant_impl.
have Hvar_hat_2_eps : 0 <= var_hat * 2 * eps.
  by rewrite -mulRA; apply: mulR_ge0; [exact: evar_ge0|lra].
rewrite /var_hat.
have ? := pr_good_gt0 pr_bad low_eps.
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
  - by apply/addR_ge0/sqrt_pos/sqrt_pos.
  - by apply/addR_ge0; apply/mulR_ge0; try apply: invR_ge0; interval.
  apply: leR_add.
    apply: (@leR_trans (sqrt (var_hat * 2 * eps * / (4 * 4 * (2 - eps))))); last first.
      rewrite sqrt_mult; [|lra|apply: invR_ge0; lra].
      rewrite sqrt_inv// (sqrt_mult (4 * 4)); [|lra|lra].
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
      + by apply: mulR_ge0; first lra; apply: mulR_ge0 => //; apply: invR_ge0; lra.
      + by rewrite mulRC /Rsqr; by lra.
      + exact: Rle_refl.
  rewrite -sqrt_inv -sqrt_mult; [|exact: Hvar_hat_2_eps|by apply: invR_ge0; lra].
  by rewrite Rsqr_sqrt; [by right|lra].
(*a8-a9*)
apply (@leR_trans ((1 - eps) * var_hat *
                   (/16 + 2 * 1/16 *
                    Rsqr (/ (4 * sqrt (2 - 1/16)) + /sqrt (1 - 1/16))))).
  apply: leR_pmul.
  - by apply mulR_ge0; [lra|exact: evar_ge0].
  - by apply addR_ge0; [lra|apply: mulR_ge0; [lra|exact: Rle_0_sqr]].
  - exact: Rle_refl.
  - apply leR_add; first exact/Rle_refl.
    apply leR_pmul; [lra|exact: Rle_0_sqr|lra|].
    apply Rsqr_bounds_le; split; first by interval.
    apply: (leR_add _ _ _ _ (leR_inv _ _ _ _) (leR_inv _ _ _ _)).
    + by apply mulR_gt0; last apply sqrt_lt_R0; lra.
    + by apply leR_wpmul2l; last apply sqrt_le_1; lra.
    + by apply sqrt_lt_R0; lra.
    + by apply sqrt_le_1; lra.
rewrite mulRC mulRA.
by apply/leR_wpmul2r/leR_wpmul2r; [exact: evar_ge0|lra|interval].
Qed.

(**md ## eqn A.10--A.11, page 63 *)
Lemma bound_empirical_variance_bad :
  16 * var <= var_hat ->
  invariant ->
  2/3 * var_hat <= \sum_(i in bad) C i * P i * tau i.
Proof.
move => var16 HiC.
have ? := pr_good_gt0 pr_bad low_eps.

have ->: \sum_(i in bad) C i * P i * tau i =
  var_hat * (\sum_(i in U) C i * P i) - (\sum_(i in good) C i * P i * tau i).
  rewrite /var_hat evarE /Var {1}/Ex.
  apply: (Rplus_eq_reg_r (\sum_(i in good) C i * P i * tau i)).
  rewrite -addRA Rplus_opp_l addR0 /bad.
  have -> : \sum_(i in ~: good) C i * P i * tau i +
            \sum_(i in good) C i * P i * tau i = \sum_(i in U) C i * P i * tau i.
    rewrite -big_union/=; last first.
      by rewrite disjoints_subset setCK.
    rewrite setUC setUCr/=.
    by apply: eq_bigl => //= u; rewrite inE.
  rewrite big_distrl/=.
  apply: eq_bigr => i _.
  rewrite /tau /mu_hat /WP Weighted.dE mulRC -mulRA; congr (_ * _).
    by rewrite sq_devE.
  by rewrite -/(Weighted.total _ _) -mulRA mulVR ?mulR1.
apply (@leR_trans (var_hat * (1 - 3 / 2 * eps) -
    \sum_(i in good) C i * P i * tau i)); last first.
  rewrite -!addR_opp; apply: Rplus_le_compat_r.
  apply leR_wpmul2l; first exact: evar_ge0.
  apply: (@leR_trans ((1 - eps / 2) * (1 - eps))); first nra.
  apply: leR_trans.
    move: (@good_mass _ _ _ _ _ C01 pr_bad low_eps HiC).
    move/(Rmult_le_compat_r (Pr P good) _ _ (Pr_ge0 _ good)).
    rewrite -Rmult_div_swap Rmult_div_l; last exact: Rgt_not_eq.
    by rewrite Pr_to_cplt pr_bad; exact.
  apply leR_sumRl => // i igood.
  + exact: Rle_refl.
  + by apply mulR_ge0 => //; apply (C01 _).1.
apply (@leR_trans ((1 - 3 / 2 * eps - 0.25 * (1 - eps)) * var_hat)); last first.
  rewrite mulRBl (mulRC var_hat).
  apply: leR_add; last by apply Ropp_le_contravar; exact: bound_empirical_variance_good.
  exact: Rle_refl.
apply (@leR_trans ((1 - 3 / 2 * 1/16 - 0.25 * (1 - 1/16)) * var_hat)); last first.
  by apply: leR_wpmul2r; [exact: evar_ge0|lra].
by apply leR_wpmul2r; [exact: evar_ge0|lra].
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
  rewrite /update_ffun-/tau_max-/tau ffunE.
  by case: ifPn => [/orP[/eqP|/eqP->]|]; lra.
by rewrite -big_split/=; apply eq_bigr => i HiS; rewrite -mulRDl addRA subRK.
Qed.

End bounding_empirical_variance.

Section update_invariant.
Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U)
  (good : {set U}) (eps : R).
Hypotheses (PC_neq0 : Weighted.total P C != 0) (C01 : is_01 C).
Let var_hat := evar X PC_neq0.
Let var := `V_[X | good].
Let tau := sq_dev X PC_neq0.
Let tau_max := sq_dev_max X PC_neq0.

Hypotheses (pr_bad : Pr P (~: good) = eps) (low_eps : eps <= 1/16)
  (var16 : 16 * var < var_hat).

Lemma sq_dev_max_neq0 : 0 < var_hat -> sq_dev_max X PC_neq0 != 0.
Proof.
rewrite /sq_dev_max => var_hat_gt0.
have /RltP HCgt0 := weighted_total_gt0 PC_neq0.
have HCge0 := ltW HCgt0.
move: var_hat_gt0.
rewrite /var_hat evarE /Var.
move=> /RltP /fsumr_gt0[i _].
rewrite Weighted.dE => /[dup] => /pmulR_lgt0' => sq_dev_gt0.
have /[apply] := pmulR_rgt0' _ (sq_RV_ge0 (X `-cst \sum_(v in U) X v * Weighted.d PC_neq0 v) i).
have /[apply] := pmulR_lgt0' _ (invR_ge0 _ (RltP _ _ HCgt0)).
have /[apply] Cigt0 := pmulR_lgt0' _ (RleP _ _ (FDist.ge0 P i)).
rewrite gt_eqF//; apply/RltP/bigmaxR_gt0; exists i; split => //.
  by rewrite gt_eqF//; exact/RltP.
rewrite sq_devE; apply/sq_dev_gt0/mulR_ge0.
  by apply/mulR_ge0 => //; apply (C01 _).1.
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
  exact: sq_dev_max_ge0.
suff H2 : \sum_(i in good) (C i * P i) * tau i <=
    (1 - eps) / 2 * (\sum_(i in ~: good) (C i * P i) * tau i).
  rewrite !update_removed_weight// !mulRDr; apply leR_add; first exact inv.
  by rewrite mulRCA; apply leR_pmul2l; [exact/divR_gt0|exact: H2].
have var16' : 16 * var <= var_hat by lra.
apply: leR_trans.
  exact: (bound_empirical_variance_good C01 pr_bad).
apply: (Rmult_le_reg_l (/((1-eps)/2))).
  by apply: invR_gt0; apply: divR_gt0 => //; lra.
rewrite mulRA mulRA mulRA Rinv_l; last by apply mulR_neq0; lra.
rewrite mul1R Rinv_div.
have -> : 2 / (1 - eps) * 0.25 * (1 - eps) = 0.5 * ((1-eps) / (1-eps)) by lra.
rewrite divRR ?mulR1; last by rewrite gt_eqF//; apply/RltP; lra.
apply: leR_trans; last first.
  exact: (bound_empirical_variance_bad C01 pr_bad).
by apply: leR_wpmul2r; [exact: evar_ge0|lra].
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
apply/RleP/mulr_ile1.
- exact/RleP/(C01 u).1.
- rewrite !coqRE subr_ge0 ler_pdivr_mulr// ?mul1r//; last first.
    by rewrite lt_neqAle eq_sym sq_dev_neq0/=;exact/RleP/sq_dev_max_ge0.
  exact/RleP/sq_dev_max_ge.
- exact/RleP/(C01 u).2.
- rewrite lerBlDr addrC -lerBlDr subrr coqRE divr_ge0//.
    exact/RleP/sq_dev_ge0.
  exact/RleP/sq_dev_max_ge0.
Qed.

End update_invariant.

Section base_case.
(* TODO: define a proper environment *)
Variables (A : finType) (P : {fdist A}) (eps : R) (good : {set A}).

Definition ffun1 : {ffun A -> R} := [ffun=> 1].
Let ffun1_subproof : [forall a, 0 <= ffun1 a]%mcR.
Proof. by apply/forallP => u; rewrite ffunE; apply/RleP. Qed.
Definition Cpos_ffun1 := @mkNNFinfun A ffun1 ffun1_subproof.

Lemma PC1_neq0 : Weighted.total P Cpos_ffun1 != 0.
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
Section filter1D.
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

Function filter1D_rec (var : R) (var_ge0: 0 <= var)
  (C : nneg_finfun U) (C01 : is_01 C) (HC : Weighted.total P C != 0)
  {measure (fun C => #| 0.-support C |) C} :=
  let empirical_mean := emean X HC in
  let empirical_variance := evar X HC in
  match empirical_variance <=? 16 * var with
  | left _ => Some empirical_mean
  | right _ =>
    let C' := update X HC in
    let C'01 := update_01 X HC C01 in
    match Weighted.total P C' !=? 0 with
    | right _ => None
    | left HC' =>  @filter1D_rec var var_ge0 C' C'01 HC'
    end
  end.
Proof.
rewrite/Weighted.total=> var var_ge0 C C01 HC evar16 h2 h3 _.
by apply (filter1D_arg_decreasing (var_ge0)).
Qed.

Definition filter1D var var_ge0 := (@filter1D_rec var var_ge0 (Cpos_ffun1 U) (@C1_is01 U) (@PC1_neq0 _ _)).

Functional Scheme filter1D_rec_ind := Induction for filter1D_rec Sort Prop.

Lemma filter1D_correct good eps :
  Pr P (~: good) = eps -> eps <= 1/16 ->
  let mu := `E_[X | good] in
  let var := `V_[X | good] in
  let var_ge0 := cvariance_ge0 X good in
  if filter1D var_ge0 is Some mu_hat
  then `| mu - mu_hat | <= sqrt (var * (2 * eps) / (2 - eps)) +
                          sqrt (16 * var * (2 * eps) / (1 - eps))
  else false.
Proof.
rewrite /filter1D => pr_bad low_eps.
have pr_good := pr_good pr_bad.
have := base_case pr_bad.
apply filter1D_rec_ind => //=.
- move=> C C01 HC evar16 _ Inv.
  apply: leR_trans; first by apply bound_mean_emean => //; rewrite pr_bad//.
  apply leR_add; first by rewrite pr_bad mulRA; right.
  apply sqrt_le_1_alt; rewrite -pr_good -Pr_to_cplt -pr_bad mulRA.
  by repeat apply leR_wpmul2r;[apply/invR_ge0;lra| |lra|apply/RleP].
- move=> C C01 HC evar16 _ PC_eq0 _ /(filter1D_inv_update C01 pr_bad low_eps (tr evar16)).
  have PC0 : forall x, update X HC x * P x = 0.
    move: PC_eq0=> /negP/negbNE; rewrite psumr_eq0; last by move=> i _; rewrite !coqRE mulr_ge0 ?nneg_finfun_ge0.
    by move/allP=> PC0 x; apply/eqP/PC0/mem_index_enum.
  rewrite /filter1D_inv.
  under eq_bigr => i ? do rewrite Rmult_plus_distr_r mulNR PC0 addR_opp subR0 mul1R.
  under [X in _ * X]eq_bigr => i _ do rewrite Rmult_plus_distr_r mulNR PC0 addR_opp subR0 mul1R.
  by move: pr_good pr_bad; rewrite /Pr; nra.
- move=> C C01 HC evar16 _ PC_neq0 _ IH Inv.
  by apply/IH/filter1D_inv_update => //; apply/tr.
Qed.

End filter1D.
