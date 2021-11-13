From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg matrix.
From mathcomp Require Import all_algebra. (* for GRing.Theory *)
From mathcomp Require boolp classical_sets. (* classical_sets for pointedType *)
From mathcomp Require Import Rstruct topology. (* topology for fct_ringType *)
Require Import Reals Lra ROrderedType.
From infotheo Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext.
From infotheo Require Import Rbigop proba fdist.
Require Import robustmean.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope proba_scope.
Local Open Scope R_scope.

Section lemma_1_4.
Variables (U : finType) (P : fdist U).

Variable X : {RV P -> R}.
Variable good : {set U}.
Variable eps : R.

Definition C0 : {ffun U -> R} := [ffun=> 1].
(*Definition C0 (i: U) := 1. *)
Definition bad := ~: good.
Definition mu := `E_[X | good].
Definition var := `V_[X | good].

Definition mu_hat C := (\sum_(i in U) P i * C i * X i) / (\sum_(i in U) P i * C i).
Definition mu_wave (C : {ffun U -> R}) := (\sum_(i in good) P i * C i * X i) / (\sum_(i in good) P i * C i).

Definition tau C := (X `-cst mu_hat C)`^2.
Definition var_hat C := (\sum_(i in U) P i * C i * tau C i) / (\sum_(i in U) P i * C i).

Lemma eqn1_1 (C: {ffun U -> R}):
  (0 < Pr P good) ->
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
  have -> : Pr P good = 1 - eps by apply/esym/subR_eq; rewrite -Hbad_ratio Pr_cplt.
    by rewrite divR1 leR_eqVlt; left.
  move => i. rewrite /C0 ffunE; lra.
Qed.

Lemma lemma1_4_start (C : {ffun U -> R}) :
  0 < \sum_(i in U) P i * C i ->
  Pr P bad = eps ->
  eps < 1 ->
  weight C -> invariant C -> invariant1 C.
Proof.
  rewrite /weight/invariant/invariant1 => HCi_gt0 HPr_bad Heps HwC HIC.
  have HPr_good: Pr P good = 1 - eps.
    by rewrite -HPr_bad Pr_of_cplt subRB subRR add0R.
  rewrite -!HPr_good.
  Print leR_trans.
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

Lemma lemma_1_4_step1 (C : {ffun U -> R}) :
  Pr P bad = eps ->
  Rsqr (mu_hat C - mu_wave C) <= `V_[X | good] * 2*eps / (1-eps).
Proof.
  move => HPr_bad.
  rewrite /mu_hat /mu_wave.
Admitted.

(*new. Alternative to Lemma lemma_1_4_step1 *)
Lemma lemma_1_4_1 (C : {ffun U -> R}) :
  Pr P bad = eps ->
  (mu_hat C - mu_wave C) <= sqrt(var * 2 * eps / (2-eps)) + sqrt(var_hat C * 2 * eps / (1-eps)).
Proof.
  move => HPr_bad.
  rewrite /mu_hat /mu_wave.
Admitted.

(*new. eqn1_1 with a C, helper for Lemma eqn_a6_a9*)
Lemma eqn1_1C (C: {ffun U -> R}):
  (0 < Pr P good) ->
  (forall a, 0 <= C a <= 1) -> 
  (\sum_(i in good) P i * C i * tau C i) / Pr P good <= var_hat C + (mu_hat C - mu_wave C)².
Proof.
move => HPgood H_0C1.
apply leR_trans with (y := `E_[tau C | good]).
  rewrite cEx_ExInd.
  apply leR_pmul2r; [by apply invR_gt0|].
  apply leR_sumRl => i Higood; last by [].
  by unfold Ind; rewrite Higood mulR1 (mulRC (tau C i)); apply leR_wpmul2r; [apply sq_RV_ge0 | 
    rewrite -{2}(mulR1 (P i)); apply leR_wpmul2l; [ | apply H_0C1]].
  by apply mulR_ge0; [apply mulR_ge0; [apply sq_RV_ge0 | apply Ind_ge0] | ].

apply/leR_eqVlt;left. unfold tau. rewrite cVarDist. admit. 
(*Print cVarDist.
apply/cVarDist.
: forall (U : finType) (P : fdist U) (X : {RV (P) -> (R)}) 
         (F : {set U}) (x : R),
       0 < Pr P F ->
       `E_[((X `-cst x) `^2) | F] = `V_[ X | F] + (`E_[X | F] - x)²   *)
exact: HPgood.
Admitted.

(*new. 1st Helper for A8.*)
Lemma var16 (C : {ffun U -> R}) :
  weight C ->
  16 * var = var_hat C. 
Proof.
  move => H.
  (*rewrite leR_eqVlt. left.
    apply sqrt_inj.
    apply sqrt_pos.*)
Admitted.

(*new. 2nd Helper for A8.*)
Lemma var1_4 (C : {ffun U -> R}) :
  weight C ->
  sqrt(var) = 1/4 * sqrt(var_hat C).
Proof.
  move => H.
Admitted.


Lemma eqn_a6_a9 (C : {ffun U -> R}) :
  weight C ->
  Pr P bad = eps ->
  \sum_(i in good) P i * C i * tau C i <= 0.32 * (1 - eps) * var_hat C.
Proof.
  move => H HPr_bad.
  (*a6*)
  have Ha6 : \sum_(i in good) P i * C i * tau C i <= (1 - eps) * (var_hat C + (mu_hat C - mu_wave C)²).
    have HPr_good: Pr P good = 1 - eps.
      by rewrite -HPr_bad Pr_of_cplt subRB subRR add0R.
    rewrite -!HPr_good Rmult_comm -leR_pdivr_mulr. 
      apply eqn1_1C. admit. (*0 < Pr P good*)
      move => a. auto.
    admit. (*0 < Pr P good*)
  
    (*a6-a7*)
  have Ha7 : \sum_(i in good) P i * C i * tau C i <= 
    (1 - eps) * (var_hat C + (sqrt(var * 2 * eps / (2-eps)) + sqrt(var_hat C * 2 * eps / (1-eps)))²).
    admit. (*by lemma_1_4_1 or lemma_1_4_step1*) 
    (*
    Ha6: \sum_(i in good) P i * C i * tau C i <=        
          (1 - eps) * (var_hat C + (mu_hat C - mu_wave C)²)
    lemma_1_4_1:                   (mu_hat C - mu_wave C) <= sqrt(var * 2 * eps / (2-eps)) + sqrt(var_hat C * 2 * eps / (1-eps)).
    *)

  (*a7-a8*)
  have Ha8 : (1 - eps) * (var + (sqrt(var * 2 * eps / (2-eps)) + sqrt(var_hat C * 2 * eps / (1-eps)))²) =
              (1 - eps) * var_hat C * (1/16 + 2 * eps * (1/(4*sqrt(2-eps)) + 1/(sqrt(1-eps)))²).
    (*by Lemma var16, change var=(1/16)*var_hat C and by Lemma var1_4, change sqrt(var)=(1/4)*sqrt(var_hat C)*)
    admit.
  
  (*a8-a9*)
  have eps1_12 : eps = 1/12. (*eps <= 1/12.*) admit.
  have Ha9_helper : (1/16 + 2 * eps * (1/(4*sqrt(2-eps)) + 1/(sqrt(1-eps)))²) <= 0.3.
    rewrite eps1_12. admit.
  
  have Ha9 : \sum_(i in good) P i * C i * tau C i <= 
              0.32 * (1 - eps) * var_hat C. admit.
  
  by exact Ha9.
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
