From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg matrix.
From mathcomp Require Import all_algebra. (* for GRing.Theory *)
From mathcomp Require boolp classical_sets. (* classical_sets for pointedType *)
From mathcomp Require Import Rstruct topology. (* topology for fct_ringType *)
Require Import Reals Lra ROrderedType.
From infotheo Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext.
From infotheo Require Import Rbigop proba fdist.
Require Import robustmean.

(******************************************************************************)
(*                                                                            *)
(*     mu_hat == empirical mean of the data, weighted mean of all the points  *)
(*    var_hat == empirical variance                                           *)
(*    mu_wave == mean of the at least 1 - epsilon fraction (under c) of       *)
(*              remaining good points                                         *)
(*  invariant == the amount of  mass removed from the good points is smaller  *)
(*              than that removed from the bad points.                        *)
(*   weight C := forall i, 0 <= C i <= 1                                      *)
(* invariant1 == consequence of invariant (p.62,l.-1)                         *)
(*   filter1d == robust mean estimation by comparing mean and variance        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope proba_scope.
Local Open Scope R_scope.

(* NB: to appear in the next release of infotheo *)
Lemma invR_ge0 (x : R) : 0 < x -> 0 <= / x.
Proof. by move=> x0; apply/ltRW/invR_gt0. Qed.

Section lemma_1_4.
Variables (U : finType) (P : fdist U).

Variable X : {RV P -> R}.
Variable good : {set U}.
Variable eps : R.

Definition C0 : {ffun U -> R} := [ffun=> 1]. (*Definition C0 (i: U) := 1. *)
Definition bad := ~: good.
Definition mu := `E_[X | good].
Definition var := `V_[X | good].

Definition mu_hat C := (\sum_(i in U) P i * C i * X i) / (\sum_(i in U) P i * C i).
Definition mu_wave (C : {ffun U -> R}) := (\sum_(i in good) P i * C i * X i) / (\sum_(i in good) P i * C i). (*TODO: rename to mu_tilda*)

Definition tau C := (X `-cst mu_hat C)`^2.
Definition var_hat C := (\sum_(i in U) P i * C i * tau C i) / (\sum_(i in U) P i * C i).

Lemma var_hat_ge0 C : (forall u, 0 <= C u) -> 0 < \sum_(i in U) P i * C i -> 0 <= var_hat C.
Proof.
by move=> C0 PC0; apply: divR_ge0 => //; apply: sumR_ge0 => i _; apply: mulR_ge0;
 [exact: mulR_ge0|exact: sq_RV_ge0].
Qed.

Lemma eqn1_1 (C : {ffun U -> R}) :
  0 < Pr P good ->
  (forall a, 0 <= C a <= 1) ->
  (\sum_(i in good) P i * C i * tau C i) / Pr P good <= var + (mu - mu_hat C)².
Proof.
move => HPgood H_0C1.
apply leR_trans with (y := `E_[tau C | good]);
  last by apply/leR_eqVlt;left;apply/cVarDist.
rewrite cEx_ExInd.
apply leR_pmul2r; [by apply invR_gt0|].
apply leR_sumRl => i Higood; last by [].
by unfold Ind; rewrite Higood mulR1 (mulRC (tau C i)); apply leR_wpmul2r; [apply sq_RV_ge0 |
 rewrite -{2}(mulR1 (P i)); apply leR_wpmul2l; [ | apply H_0C1]].
by apply mulR_ge0; [apply mulR_ge0; [apply sq_RV_ge0 | apply Ind_ge0] | ].
Qed.

Definition tau_max (C : {ffun U -> R}) := \rmax_(i in [set: U]) tau C i.

Definition arg_tau_max (C : {ffun U -> R}) :=
  [arg max_(i > (fdist_supp_choice P) in [set: U]) tau C i]%O.

Definition update (C : {ffun U -> R}) :=
  [ffun i => C i * (1 - tau C i / tau_max C)].

Definition invariant (C : {ffun U -> R}) :=
  (\sum_(i in good) P i * (1 - C i) <= (1 - eps)/2 * \sum_(i in bad) P i * (1 - C i)).
Definition invariant1 C :=
  (1 - eps <= (\sum_(i in good) P i * C i) / (\sum_(i in U) P i * C i)).
Definition weight (C : {ffun U -> R}) :=
  (forall i, 0 <= C i <= 1).

Lemma base_case: Pr P bad = eps -> invariant C0 /\ invariant1 C0 /\ weight C0.
Proof.
  move => Hbad_ratio.
  rewrite /invariant.
  apply conj.
    under eq_bigr do rewrite ffunE subRR mulR0.
    rewrite big1; last by [].
    under eq_bigr do rewrite ffunE subRR mulR0.
    rewrite big1; last by [].
    rewrite mulR0. apply leRR.
  apply conj.
  rewrite /invariant1.
  have ->: (\sum_(i in good) P i * C0 i) = Pr P good
    by under eq_bigr do rewrite /C0 ffunE mulR1.
  have ->: (\sum_(i in U) P i * C0 i) = 1.
    under eq_bigr do rewrite /C0 ffunE mulR1.
    exact: FDist.f1.
  by rewrite Pr_to_cplt Hbad_ratio divR1; exact/leRR.
  move => i. rewrite /C0 ffunE; lra.
Qed.

Lemma lemma1_4_start (C : {ffun U -> R}) :
  0 < \sum_(i in U) P i * C i ->
  Pr P bad = eps ->
  eps < 1 ->
  weight C -> invariant C -> invariant1 C.
Proof.
  rewrite /weight/invariant/invariant1 => HCi_gt0 HPr_bad Heps HwC HIC.
  have HPr_good : Pr P good = 1 - eps by rewrite Pr_to_cplt HPr_bad.
  rewrite -!HPr_good.
  apply leR_trans with (y := (Pr P good / 2 * (1 + Pr P good + (\sum_(i in bad) P i * C i))) / (\sum_(i in U) P i * C i)).
  apply leR_pmul2r with (m := (\sum_(i in U) P i * C i) * 2).
    by apply mulR_gt0.
  rewrite !mulRA !(mulRC _ 2) -(mulRA _ (/ _)) mulVR; last by apply gtR_eqF.
  rewrite mulR1 !mulRA (mulRC _ (/2)) mulRA mulVR; last by apply gtR_eqF.
  rewrite mul1R -addRR mulRDl -addRA mulRDr.
  apply leR_add.
    apply leR_pmul2l; first by rewrite HPr_good; lra.
    rewrite -(Pr_setT P) /Pr sumR_setT.
    by apply leR_sumRl; move => i _; first by
      rewrite -{2}(mulR1 (P i));
      apply leR_wpmul2l; [|apply HwC].
  apply leR_pmul2l; first by rewrite HPr_good; lra.
    rewrite /Pr addRC -bigID2.
    apply leR_sumR => i HiU.
    destruct (i \in good).
      simpl.
      by rewrite -{2}(mulR1 (P i)); apply leR_pmul; try apply HwC; auto; right.
    simpl. by right.
  apply leR_pmul2r; first by apply invR_gt0.
  apply Ropp_le_cancel.
  rewrite {2}HPr_good addRA -addRA -HPr_bad mulRDr oppRD addRC.
  apply leR_subl_addr.
  rewrite /Rminus oppRK -mulRN addRC {1}/Rdiv -mulRA mulVR; last by apply gtR_eqF.
  rewrite mulR1 oppRD oppRK !big_morph_oppR.
  rewrite -!big_split. simpl.
  have H: forall S, \sum_(i in S) (P i + - (P i * C i)) = \sum_(i in S) P i * (1 - C i).
  move => p S. apply eq_bigr => i _.
    by rewrite -{1}(mulR1 (P i)) -mulRN -mulRDr.
  by rewrite !H HPr_good.
Qed.

Local Definition weightedf (C : {ffun U -> R}) : {ffun U -> R} :=
  [ffun i => P i * C i / \sum_(i in U) P i * C i].

Local Lemma weightedf0 (C : {ffun U -> R})
  (PC0 : 0 < \sum_(i in U) P i * C i) (C0 : forall u, 0 <= C u) :
  [forall a, 0 <b= weightedf C a].
Proof.
apply/forallP => u; apply/leRP; rewrite /weightedf ffunE.
by apply: mulR_ge0; [apply: mulR_ge0 => //|apply/invR_ge0].
Qed.

Local Lemma weightedf1 (C : {ffun U -> R})
  (PC0 : 0 < \sum_(i in U) P i * C i) (C0 : forall u, 0 <= C u) :
  \sum_(a in U) mkPosFfun (weightedf0 PC0 C0) a == 1.
Proof.
rewrite /= /weightedf.
under eq_bigr do rewrite ffunE.
by rewrite -big_distrl /= -divRE divRR//; exact/gtR_eqF.
Qed.

Definition weightedP (C : {ffun U -> R})
  (PC0 : 0 < \sum_(i in U) P i * C i) (C0 : forall u, 0 <= C u) :
  {fdist U} := FDist.mk (weightedf1 PC0 C0).

Lemma lemma_1_4_step1 (C : {ffun U -> R}) :
  (0 < \sum_(i in U) P i * C i) ->
  (forall u, 0 <= C u) ->
  invariant1 C ->
  0 <= eps < 1 ->
  Pr P bad = eps ->
  Rsqr (mu_hat C - mu_wave C) <= var_hat C * 2 * eps / (1 - eps).
Proof.
move=> PC0 C0 invC [eps0 eps1] HPr_bad.
suff h : `| mu_hat C - mu_wave C | <= sqrt (var_hat C * 2 * eps / (1 - eps)).
  rewrite Rsqr_abs -[X in _ <= X]Rsqr_sqrt; last first.
    apply: mulR_ge0; last exact/invR_ge0/subR_gt0.
    by apply: mulR_ge0 => //; apply: mulR_ge0 => //; [exact: var_hat_ge0|lra].
  by apply/Rsqr_incr_1 => //; [exact/normR_ge0|exact: sqrt_pos].
pose delta := 1 - eps.
have {1}-> : eps = 1 - delta by rewrite subRB subRR add0R.
rewrite -/delta distRC.
pose P' : {fdist U} := weightedP PC0 C0.
pose X' : {RV P' -> R} := X.
have mu_hatE : mu_hat C = `E X'. (* TODO: lemma? *)
  rewrite /mu_hat /Ex /X' /ambient_dist /P' /= /weightedf.
  under [in RHS]eq_bigr do rewrite ffunE !mulRA -divRE.
  rewrite -big_distrl/= -divRE; congr (_ / _).
  by under eq_bigr do rewrite mulRAC (mulRC (P _)).
rewrite mu_hatE.
have -> : mu_wave C = `E_[X' | good].
  rewrite /mu_wave cEx_ExInd /Ex /ambient_dist /Ind /X' {1}/P' /= /weightedf.
  under [in RHS]eq_bigr do rewrite ffunE !mulRA.
  rewrite -big_distrl /= [in RHS]divRE -mulRA; congr (_ * _).
    rewrite big_mkcond /=; apply eq_bigr => u _.
    by case: ifP => _; rewrite !(mulR0,mul0R,mulR1)// mulRAC (mulRC (P _)).
  rewrite /Pr /= /weightedf.
  under [in X in _ = _ * X]eq_bigr do rewrite ffunE.
  rewrite -big_distrl /= invRM; last 2 first.
    - apply/gtR_eqF.
      admit.
    - exact/invR_neq0'/gtR_eqF.
  rewrite mulRCA invRK; last exact/gtR_eqF.
  by rewrite mulVR ?mulR1//; exact/gtR_eqF.
have -> : var_hat C = `V X'. (*TODO: turn this into a lemma*)
  rewrite /var_hat divRE big_distrl /=; apply eq_bigr => u _ /=.
  by rewrite /weightedf /= ffunE [in RHS]mulRCA -mulRA /tau mu_hatE.
apply: resilience => //.
- by rewrite /delta; apply/subR_gt0.
- rewrite /delta -HPr_bad -Pr_to_cplt /Pr /P' /= /weightedf.
  under [in X in _ <= X]eq_bigr do rewrite ffunE.
  apply: (@leR_trans (1 - eps)).
    by rewrite -/(Pr P good) Pr_to_cplt HPr_bad; exact: leRR.
  by move: invC; rewrite /invariant1 -big_distrl.
- rewrite /Pr /P' /= /weightedf.
  under [in X in X != _]eq_bigr do rewrite ffunE.
  rewrite -big_distrl/= -divRE; apply/ltR_eqF/ltR_pdivr_mulr => //.
  rewrite mul1R [in X in _ < X](bigID (fun x => x \in good))/=.
  apply/ltR_addl.
  admit.
Admitted.

Lemma eqn_a6_a9 (C : {ffun U -> R}) :
  weight C ->
  Pr P bad = eps ->
  \sum_(i in good) P i * C i * tau C i <= 0.32 * (1 - eps) * var_hat C.
Proof.
Admitted.

Lemma eqn1_3_4 (C : {ffun U -> R}) (S: {set U}):
  let C' := update C in
  \sum_(i in S) P i * (1 - C' i) =
    (\sum_(i in S) P i * (1 - C i)) + 1 / tau_max C * (\sum_(i in S ) P i * (C i * tau C i)).
Proof.
  move => C'.
  have <-: \sum_(i in S) P i * (C i - C' i) = 1 / tau_max C * (\sum_(i in S) P i * (C i * tau C i)).
    rewrite /C' /update big_distrr.
    apply eq_bigr => i _. simpl.
    by rewrite /Rminus /Rdiv ffunE (mulRDr (C i)) mulR1 oppRD addRA mulRN oppRK addRN add0R !mulRA !mulR1 mul1R mulRC !mulRA.
  rewrite -big_split.
  apply eq_bigr => i HiS. simpl.
  rewrite -mulRDr. congr (_*_). lra.
Qed.

Lemma lemma_1_5 (C : {ffun U -> R}) :
  let C' := update C in
  0 < tau_max C ->
  \sum_(i in good) P i * (C i * tau C i) <= (1 - eps) / 2 * (\sum_(i in bad) P i * (C i * tau C i)) ->
  invariant C -> invariant C'.
Proof.
  rewrite /invariant.
  move => H0 H1 IH1.
  rewrite !eqn1_3_4 !mulRDr.
  apply leR_add; first by [].
  rewrite (mulRC ((1 - eps) / 2)) -mulRA.
  apply leR_pmul2l; first by rewrite /Rdiv mul1R; apply invR_gt0.
  by rewrite mulRC.
Qed.

(*
  rewrite /update => i.
  split.
  apply mulR_ge0.
  apply IH3.
  apply leR_trans with (y:=1 - (\rmax_(i0 in [set: U]) tau C i0) / (\rmax_(i0 in [set: U]) tau C i0)).
  have [Hmax_gt0|Hmax_eq0]: 0 <= (\rmax_(i0 in [set: U]) tau C i0).
  admit.
  by rewrite divRR; [rewrite subRR; apply leR_eqVlt; left|apply gtR_eqF].
  rewrite -!Hmax_eq0 /Rdiv mul0R; lra.
  apply leR_add. by right.
  apply Ropp_le_contravar.
  apply leR_wpmul2r.
  admit.
  admit.
  apply leR_bigmaxR.
Admitted.
*)

Require Import Program.Wf.

Local Obligation Tactic := idtac.
Program Fixpoint filter1d (C : {ffun U -> R}) {measure #| 0.-support C | } :=
  match #| 0.-support C | with
  | 0      => None
  | S gas' => if Rleb (var_hat C) var
              then Some (mu_hat C)
              else filter1d (update C)
  end.
Next Obligation.
move=> C _ _ _ _.
(*
X := 0.-support (update C)
Y := 0.-support C
X \subset Y
arg_tau_max \notin X
arg_tau_max \in Y
*)
Admitted.
Next Obligation. Admitted.

(*
Definition filter1d gas :=
  let fix filter1d_iter gas (C : {ffun U -> R}) := match gas with
    0      => None
  | S gas' => if Rleb (var_hat C) var then Some (mu_hat C) else filter1d_iter gas' (update C)
  end in filter1d_iter gas C0.
*)

Lemma first_note (C: {ffun U -> R}):
  invariant C -> 1 - eps <= (\sum_(i in good) C i * P i) / (\sum_(i in U) C i * P i).
Admitted.

End lemma_1_4.
