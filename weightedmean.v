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

(* TODO: move to infotheo *)
Section move_to_infotheo.
Section rExtrema. (* Reals_ext.v *)
Local Open Scope ring_scope.
Variables (I : finType) (i0 : I) (F : I -> R) (P : {pred I}).
Lemma arg_rmax2_cond : P i0 -> forall j, P j -> (F j <= F [arg max_(i > i0 | P i) F i]%O)%O.
Proof.
move=> Pi0 j Pj; case: (@Order.TotalTheory.arg_maxP _ _ I i0 P F Pi0) => i _.
by move/(_ j Pj).
Qed.
End rExtrema.

Section nneg_fun. (* Reals_ext.v *)

Lemma nneg_fun_le0 (I : Type) (F : nneg_fun I) i : (F i == 0) = (F i <= 0)%mcR.
Proof.
apply/sameP/idP/(iffP idP); first by move/eqP->.
by move/RleP/Rle_antisym/(_ (nneg_f_ge0 _ _)) ->.
Qed.

Variables (I : eqType) (r : seq I) (P : pred I) (F : nneg_fun I).
Lemma nneg_fun_bigmaxR0P :
  reflect (forall i : I, i \in r -> P i -> F i = 0)
          (\rmax_(i <- r | P i) F i == 0).
Proof.
apply: (iffP idP) => [/eqP H i ir Pi| H].
- apply/eqP; rewrite nneg_fun_le0 -coqRE -H; apply/RleP.
  rewrite -big_filter; apply: leR_bigmaxR.
  by rewrite mem_filter ir Pi.
- rewrite -big_filter big_seq.
  under eq_bigr=> i do rewrite mem_filter=> /andP [] /[swap] /(H i) /[apply] ->.
  by rewrite -big_seq big_const_seq iter_fix // maxRR.
Qed.
End nneg_fun.

Section nneg_finfun. (* Reals_ext.v *)
Local Open Scope R_scope.
Lemma nneg_finfun_le0 (I : finType) (F : nneg_finfun I) i : (F i == 0) = (F i <= 0)%mcR.
Proof.
apply/idP/idP => [/eqP -> //|].
case: F => F /= /forallP /(_ i).
by rewrite eq_le coqRE => -> ->.
Qed.

Variables (I : finType) (r : seq I) (P : pred I) (F : nneg_finfun I).
Fail Check F : pos_fun _. (* Why no coercion pos_ffun >-> pos_fun? *)
Lemma pos_ffun_bigmaxR0P :
  reflect (forall i : I, i \in r -> P i -> F i = 0)
          (\rmax_(i <- r | P i) F i == 0).
apply: (iffP idP) => [/eqP H i ir Pi|H].
- apply/eqP; rewrite nneg_finfun_le0 -coqRE -H.
  rewrite -big_filter; apply/RleP; apply: leR_bigmaxR.
  by rewrite mem_filter ir Pi.
- rewrite -big_filter big_seq.
  under eq_bigr=> i do rewrite mem_filter=> /andP [] /[swap] /(H i) /[apply] ->.
  by rewrite -big_seq big_const_seq iter_fix // maxRR.
Qed.
End nneg_finfun.
End move_to_infotheo.

Module Weighted.
Section def.
Variables (A : finType) (p : prob R) (d0 : {fdist A}) (c : nneg_finfun A).
Definition total := \sum_(a in A) c a * d0 a.
Hypothesis total_neq0 : total != 0.
Definition f := [ffun a => c a * d0 a / total].
Lemma total_gt0 : (0 < total)%mcR.
Proof.
rewrite lt_neqAle eq_sym total_neq0/=.
rewrite /total.
rewrite sumr_ge0// => i _. 
apply/mulr_ge0/FDist.ge0.
by case: c => c' /= /forallP.
Qed.

Lemma f0 a : (0 <= f a)%mcR.
Proof.
rewrite ffunE /f coqRE divr_ge0//; last first.
  rewrite ltW//. exact  total_gt0.
rewrite coqRE mulr_ge0 => //.
case: c => c' /= /forallP. exact.
Qed.

Lemma f1 : \sum_(a in A) f a = 1.
Proof.
rewrite /f.
under eq_bigr do rewrite ffunE divRE.
by rewrite -big_distrl /= mulRV.
Qed.
Definition d : {fdist A} := locked (FDist.make f0 f1).
Lemma dE a : d a = c a * d0 a / total.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End def.
Section prop.
Variables (A : finType) (d0 : {fdist A}) (p : prob R)  (c : nneg_finfun A).
(*
Lemma fdist1 (g : 'I_n -> fdist A) a : d (FDist1.d a) g = g a.
Proof.
apply/fdist_ext => a0; rewrite dE (bigD1 a) //= FDist1.dE eqxx mul1R.
by rewrite big1 ?addR0 // => i ia; rewrite FDist1.dE (negbTE ia) mul0R.
Qed.
Lemma cst (e : {fdist 'I_n}) (a : {fdist A}) : d e (fun=> a) = a.
Proof. by apply/fdist_ext => ?; rewrite dE -big_distrl /= FDist.f1 mul1R. Qed.
*)
End prop.
End Weighted.

(*
Variable (A : finType) (d0 : {fdist A}) (c : pos_ffun A) (ax : WeightedFDist.axiom d0 c).
Definition wd := WeightedFDist.d ax.
!!!!!
*)

Section lemma_1_4.
Variables (U : finType) (P : {fdist U}).

Variable X : {RV P -> R}.

Variable C : nneg_finfun U.
Hypothesis PC_neq0 : Weighted.total P C != 0.
Let P' := Weighted.d PC_neq0.

Definition mu_hat := `E (X : {RV P' -> R}).

Lemma mu_hatE :
  mu_hat = (\sum_(i in U) P i * C i * X i) / \sum_(i in U) P i * C i.
Proof.
rewrite /mu_hat /Ex /ambient_dist divRE.
rewrite big_distrl/=; apply: eq_bigr => u _.
rewrite -mulRA mulRCA; congr (_ * _).
rewrite /P' Weighted.dE (mulRC _ (P u)) -divRE; congr (_ / _).
by under eq_bigr do rewrite mulRC.
Qed.

Definition tau := (X `-cst mu_hat)`^2.
Definition var_hat := (\sum_(i in U) P i * C i * tau i) / (\sum_(i in U) P i * C i).

Lemma var_hat_ge0 : (forall u, 0 <= C u) -> 0 < \sum_(i in U) P i * C i -> 0 <= var_hat.
Proof.
move=> C0 PC0; apply: divR_ge0 => //. 
apply/RleP; apply: sumr_ge0 => i _.
apply: mulr_ge0.
  by rewrite coqRE; apply: mulr_ge0 => //; apply/RleP; apply: C0.
by rewrite /tau; apply/RleP; apply: sq_RV_ge0.
Qed.

Lemma tau_ge0 i : 0 <= tau i.
Proof. rewrite /tau sq_RV_pow2; exact: pow2_ge_0. Qed.

Definition tau_max := \rmax_(i in [set: U] | C i != 0) tau i.
(*
Definition tau_max' (C : {ffun U -> R}) :=
  \big[Num.max/0]_(i in [set: U]) tau C i.

(* to be generalize to something like big_RmaxE? *)
Lemma tau_maxE C : tau_max C = tau_max' C.
Proof.
rewrite /tau_max /tau_max'; apply big_ind2=> //.
by move=> ? ? ? ? -> ->; rewrite RmaxE.
Qed.
*)

Lemma tau_max_ge0 : 0 <= tau_max.
Proof.
rewrite /tau_max -big_filter; apply bigmaxR_ge0=> *; exact:tau_ge0.
Qed.

Definition arg_tau_max :=
  [arg max_(i > (fdist_supp_choice P) in [set: U]) tau i]%O.

(*
Definition update (C : {ffun U -> R}) : {ffun U -> R} :=
  [ffun i => C i * (1 - tau C i / tau_max C)].
*)
Definition update_ffun : {ffun U -> R} :=
  [ffun i => if (tau_max == 0) || (C i == 0) then 0 else
            C i * (1 - tau i / tau_max)].

Lemma nneg_finfun_ge0 (c : nneg_finfun U) i : 0 <= c i.
Proof.
apply/RleP.
case: c => c' /= /forallP. exact.
Qed.

Lemma update_pos_ffun : [forall a, 0 <= update_ffun a]%mcR.
Proof.
apply/forallP=> u; apply/RleP.
rewrite /update_ffun ffunE.
have [_|/=] := eqVneq tau_max 0 => //=.
move/eqP; rewrite eqR_le => /boolp.not_andP []; last by move/(_ tau_max_ge0).
rewrite -ltRNge => tau_max_gt0.
case: ifPn=> [|Cu0]; first by move=> _.
apply mulR_ge0; first exact: nneg_finfun_ge0.
rewrite subR_ge0 leR_pdivr_mulr //.
rewrite mul1R /tau_max.
rewrite -big_filter.
apply: (leR_bigmaxR _ tau).
by rewrite mem_filter inE/= mem_index_enum andbT.
Qed.

Definition update : nneg_finfun U := mkNNFinfun update_pos_ffun.

(* Note: this theorem does not hold in general: it should only work
   when the empirical variance is at least 16 times the actual variance *)
Lemma update_valid_weight : Weighted.total P update != 0.
Proof.
rewrite /Weighted.total/update/update_ffun/=.
move=> [:tmp].
rewrite gt_eqF// lt_neqAle; apply/andP; split.
  rewrite eq_sym psumr_neq0; last first.
    abstract: tmp.
    move=> u uU; rewrite ffunE/=; case: ifPn; first by rewrite mul0R.
    rewrite negb_or => /andP[taumax0 Cu0].
    rewrite mulr_ge0// mulr_ge0//.
      exact/RleP/nneg_finfun_ge0.
    rewrite subr_ge0 RdivE// ler_pdivrMr ?mul1r//.
      rewrite /tau_max.
      (* Unset Printing Notations. *)
      (* rewrite big_mkcond. *)
      (* apply: bigmax_sup. *)
      admit.
    rewrite lt_neqAle eq_sym taumax0/=.
    admit.
  apply/hasP.
  admit.
apply: sumr_ge0.
exact: tmp.
Admitted.

(* TODO: new section *)
Variable good : {set U}.
Variable eps : R.

Definition eps_max := 1/16.

Definition C0 : {ffun U -> R} := [ffun=> 1]. (*Definition C0 (i: U) := 1. *)
Definition bad := ~: good.
Definition mu := `E_[X | good].
Definition var := `V_[X | good].

Definition mu_wave :=
  (\sum_(i in good) P i * C i * X i) / (\sum_(i in good) P i * C i). (*TODO: rename to mu_tilda*)

Lemma eqn1_1 :
  0 < Pr P good ->
  (forall a, 0 <= C a <= 1) ->
  (\sum_(i in good) P i * C i * tau i) / Pr P good <= var + (mu - mu_hat)².
Proof.
move => HPgood H_0C1.
apply leR_trans with (y := `E_[tau | good]);
  last by apply/leR_eqVlt;left;apply/cVarDist.
rewrite cEx_ExInd.
apply leR_pmul2r; [by apply invR_gt0|].
apply leR_sumRl => i Higood; last by [].
by rewrite /Ind/mul_RV Higood mulR1 (mulRC (tau i)); apply leR_wpmul2r; [apply sq_RV_ge0 |
 rewrite -{2}(mulR1 (P i)); apply leR_wpmul2l; [ | apply H_0C1]].
by apply mulR_ge0; [apply mulR_ge0; [apply sq_RV_ge0 | apply Ind_ge0] | ].
Qed.

Definition invariant (C : {ffun U -> R}) :=
  (\sum_(i in good) P i * (1 - C i) <= (1 - eps) / 2 * \sum_(i in bad) P i * (1 - C i)).
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
    rewrite mulR0. exact/RleP.
  apply conj.
  rewrite /invariant1.
  have ->: (\sum_(i in good) P i * C0 i) = Pr P good
    by under eq_bigr do rewrite /C0 ffunE mulR1.
  have ->: (\sum_(i in U) P i * C0 i) = 1.
    under eq_bigr do rewrite /C0 ffunE mulR1.
    exact: FDist.f1.
  by rewrite Pr_to_cplt Hbad_ratio divR1; exact/RleP.
  move => i. rewrite /C0 ffunE; lra.
Qed.

Lemma lemma1_4_start :
  0 < \sum_(i in U) P i * C i ->
  Pr P bad = eps ->
  eps < 1 ->
  weight C -> invariant C -> invariant1 C.
Proof.
  rewrite /weight/invariant/invariant1 => HCi_gt0 HPr_bad Heps HwC HIC.
  have HPr_good : Pr P good = 1 - eps by rewrite Pr_to_cplt HPr_bad.
  rewrite -!HPr_good.
  apply leR_trans with (y := (Pr P good / 2 * (1 + Pr P good + (\sum_(i in bad) P i * C i))) / (\sum_(i in U) P i * C i)).
  apply leR_pmul2r with (m := (\sum_(i in U) P i * C i) * 2);
    first by apply mulR_gt0.
  rewrite !mulRA !(mulRC _ 2) -(mulRA _ (/ _)) mulVR; last by apply gtR_eqF.
  rewrite mulR1 !mulRA (mulRC _ (/2)) mulRA mulVR; last by apply gtR_eqF.
  rewrite mul1R -addRR mulRDl -addRA mulRDr.
  apply leR_add.
    apply leR_pmul2l; first by rewrite HPr_good; lra.
    rewrite -(Pr_setT P) /Pr.
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

Lemma sumCi_ge0 : weight C -> 0 <= \sum_(i in U) P i * C i.
Proof.
move=> Hweight.
by apply/RleP; apply sumr_ge0 => i _;
  rewrite coqRE mulr_ge0//; apply /RleP; apply Hweight.
Qed.

(* Ale: I turned these into lemmas and definitions, but maybe it's better to refactor *)
Lemma C0' : (forall u, 0 <= C u) -> [forall a, 0 <= C a]%mcR.
Proof. by move=> h; apply/forallP => u; apply/RleP. Qed.
Definition Cpos_fun h := mkNNFinfun (C0' h).
Definition X' : {RV P' -> R} := X.
Lemma h1 h : Weighted.total P (Cpos_fun h) != 0.
Proof.
move: PC_neq0.
rewrite /Weighted.total.
by under eq_bigr do rewrite mulRC.
Qed.

Lemma mu_wave_expectation : mu_wave = `E_[X' | good].
Proof.
  rewrite /mu_wave cEx_ExInd /Ex /ambient_dist /Ind /X'.
  rewrite 2!divRE 2!big_distrl /= big_mkcond /=; apply: eq_bigr => u _.
  case: ifPn => ugood; last by rewrite !(mulR0,mul0R).
  rewrite mulR1 -mulRA mulRCA -[in RHS]mulRA; congr (_ * _).
  rewrite {1}/P' {1}Weighted.dE /Cpos_fun /= (mulRC _ (P u)).
  rewrite [in RHS]divRE -[in RHS]mulRA; congr (_ * _).
  rewrite /Pr /P'.
  under [in RHS]eq_bigr do rewrite Weighted.dE.
  have [/eqP PC0|PC0] := boolP (\sum_(i in good) P i * C i == 0).
    rewrite PC0 Rinv_0.
    under eq_bigr do rewrite RdivE'.
    rewrite -big_distrl/=.
    under eq_bigr do rewrite mulRC.
    by rewrite PC0 mul0R Rinv_0 mulR0.
  rewrite -big_distrl /= invRM //; last 2 first.
    by under eq_bigr do rewrite mulRC.
    exact/eqP/invR_neq0/eqP.
  rewrite invRK// mulRCA mulVR// mulR1.
  by under eq_bigr do rewrite mulRC.
Qed.

Lemma var_hat_variance : var_hat = `V X'.
Proof.
  rewrite /var_hat divRE big_distrl /=; apply eq_bigr => u _ /=.
  rewrite mulRAC (mulRC _ (tau u)) /tau; congr (_ * _).
  rewrite /ambient_dist /P' Weighted.dE /Cpos_fun /=.
  rewrite -divRE (mulRC _ (C u)); congr (_ / _).
  by under eq_bigr do rewrite mulRC.
Qed.

Lemma lemma_1_4_step1 :
  0 < \sum_(i in U) P i * C i (* NB: this can be proved from the termination condition *) ->
  (forall u, 0 <= C u) ->
  invariant1 C ->
  0 <= eps < 1 ->
  Pr P bad = eps ->
  Rsqr (mu_hat - mu_wave) <= var_hat * 2 * eps / (1 - eps).
Proof.
move=> PC0 C0 invC [eps0 eps1] HPr_bad.
have [good0|good_neq0] := eqVneq (\sum_(i in good) P i * C i) 0.
  by move: invC; rewrite /invariant1 good0 div0R => /subR_le0; rewrite leRNgt.
have [bad0|bad_neq0] := eqVneq (\sum_(i in bad) P i * C i) 0.
  rewrite mu_hatE /mu_wave.
  rewrite [in X in Rsqr (_ / X - _)](bigID [pred x | x \in bad]) /= bad0 add0R.
  rewrite [in X in Rsqr (_ / X - _)](eq_bigl [pred x | x \in good]); last first.
    by move=> *; rewrite /= /bad inE negbK.
  rewrite -mulRBl.
  rewrite [in X in Rsqr ((X - _) / _)](bigID [pred x | x \in bad]) /=.
  rewrite [in X in Rsqr ((_ + X - _) / _)](eq_bigl [pred x | x \in good]); last first.
    by move=> *; rewrite /= /bad inE negbK.
  rewrite addRK.
  have badge0: (forall i : U, i \in bad -> (0 <= (P i * C i)%coqR)%mcR).
    move=> i _; rewrite !RmultE mulr_ge0//; apply/RleP; exact: C0.
  move: bad0 => /(psumr_eq0P badge0) bad0.
  rewrite big1 ?mul0R ?div0R? Rsqr_0; last by move=> u ubad; rewrite bad0// mul0R.
  apply: mulR_ge0; last exact/invR_ge0/subR_gt0.
  apply: mulR_ge0 => //; apply: mulR_ge0; last by lra.
  exact: var_hat_ge0.
suff h : `| mu_hat - mu_wave | <= sqrt (var_hat * 2 * eps / (1 - eps)).
  rewrite Rsqr_abs -[X in _ <= X]Rsqr_sqrt; last first.
    apply: mulR_ge0; last exact/invR_ge0/subR_gt0.
    by apply: mulR_ge0 => //; apply: mulR_ge0 => //; [exact: var_hat_ge0|lra].
  by apply/Rsqr_incr_1 => //; [exact/normR_ge0|exact: sqrt_pos].
pose delta := 1 - eps.
have {1}-> : eps = 1 - delta by rewrite subRB subRR add0R.
rewrite -/delta distRC.
rewrite mu_wave_expectation var_hat_variance.
apply: resilience => //.
- by rewrite /delta; apply/subR_gt0.
- rewrite /delta -HPr_bad -Pr_to_cplt /Pr /P' /=.
  under [in X in _ <= X]eq_bigr do rewrite Weighted.dE /= mulRC.
  apply: (@leR_trans (1 - eps)).
    by rewrite -/(Pr P good) Pr_to_cplt HPr_bad; apply/RleP.
  move: invC; rewrite /invariant1 -big_distrl /=.
  by under [X in _ <= _ / X -> _]eq_bigr do rewrite mulRC.
- rewrite /Pr /P' /=.
  under [in X in X < 1]eq_bigr do rewrite Weighted.dE /=.
  rewrite -big_distrl/= -divRE; apply/ltR_pdivr_mulr => //.
    rewrite ltR_neqAle; split; first exact/nesym/eqP.
    by apply/RleP/sumr_ge0 => u _; rewrite mulr_ge0//; exact/RleP/nneg_finfun_ge0.
  rewrite mul1R.
  rewrite /Weighted.total [in X in _ < X](bigID (fun x => x \in good))/=.
  apply/ltR_addl.
  under eq_bigr do rewrite mulRC.
  rewrite ltR_neqAle; split.
    apply/nesym/eqP.
    by apply: contra bad_neq0 => /eqP <-; apply/eqP/eq_bigl => u; rewrite !inE.
  by apply/RleP/sumr_ge0 => u _; rewrite mulr_ge0//; exact/RleP/nneg_finfun_ge0.
Qed.

Lemma cExE F : `E_[X | F] = (\sum_(u in F) X u * P u) / Pr P F.
Proof.
rewrite cEx_ExInd.
congr (_ / _).
rewrite /Ex /ambient_dist /Ind.
under eq_bigr => i _ do rewrite /mul_RV 2!fun_if if_arg mulR0 mul0R mulR1.
rewrite [in RHS]big_mkcond /=.
by apply eq_bigr => i _. 
Qed.

Lemma good_mass : 
  Pr P bad = eps ->
  eps < eps_max ->
  weight C ->
  invariant C ->
  1 - eps/2 <= (\sum_(i in good) P i * C i) / Pr P good.
Proof.
rewrite /eps_max/weight => HPr_bad Hlow_eps HwC Hinv.
have HPr_good: Pr P good = 1 - eps.
  by rewrite -HPr_bad Pr_of_cplt subRB subRR add0R.
apply leR_trans with (y := 1 - (1-eps)/2/Pr P good * Pr P bad).
  by rewrite HPr_bad HPr_good -!mulRA mulRC (mulRC (/(_-_))) mulRA -mulRA mulVR; [rewrite mulR1 mulRC; right|apply /gtR_eqF; lra].
apply leR_trans with (y := 1 - (1-eps)/2/Pr P good * \sum_(i in bad) P i * (1 - C i)).
  rewrite leR_add2l leR_oppl oppRK leR_pmul2l;
    last (rewrite HPr_good /Rdiv mulRC mulRA mulVR; [lra|rewrite gt_eqF//; apply/RltP; lra]).
  apply leR_sumR => i Hi_bad.
  rewrite -{2}(mulR1 (P i)).
  move: (FDist.ge0 P i); move/RleP => [HPi_gt0|HPi_eq0].
    by apply/RleP; rewrite !coqRE ler_wpM2l// gerBl//; move: (HwC i).1 => /RleP.
  by rewrite -HPi_eq0 !mul0R.
rewrite -HPr_good /Rdiv -(mulRA (Pr P good)) (mulRC (/2)) mulRA mulRV; last by (apply gtR_eqF; lra).
apply leR_pmul2r with (m := Pr P good);
  [rewrite HPr_good; lra|rewrite -(mulRA _ (/ Pr P good)) mulVR; [rewrite mul1R mulR1|apply gtR_eqF; lra]].
rewrite mulRDl mul1R {2}HPr_good mulRC mulRN.
apply Rplus_le_reg_l with (r := -Pr P good).
rewrite addRA (addRC (- _)) addRN add0R mulRA.
apply leR_oppl.
rewrite oppRD oppRK /Pr -(mul1R (- _)) mulRN -mulNR big_distrr -big_split; simpl.
by under eq_bigr => i _; [
  rewrite mulNR mul1R -mulRN -{1}(mulR1 (P i)) -mulRDr;over|].
Qed.

Lemma lemma_1_4_step2 :
  Pr P bad = eps ->
  eps < eps_max ->
  weight C ->
  invariant C ->
  Rsqr (mu - mu_wave) <= var_hat * 2*eps / (2-eps).
Proof.
rewrite /eps_max/weight => HPr_bad Hlow_eps HwC Hinv.
have HPr_good: Pr P good = 1 - eps.
  by rewrite -HPr_bad Pr_of_cplt subRB subRR add0R.
rewrite /invariant in Hinv.
suff h : `| mu - mu_wave | <= sqrt (var_hat * 2 * eps / (2 - eps)).
  apply sqrt_le_0; first by apply Rle_0_sqr.
  rewrite var_hat_variance.
  repeat apply mulR_ge0;
    [exact: variance_nonneg|lra|rewrite -HPr_bad; apply Pr_ge0|apply invR_ge0; lra].
  by rewrite sqrt_Rsqr_abs.
rewrite distRC mu_wave_expectation.
rewrite -cEx_trans_min_RV.
rewrite -sqrt_Rsqr_abs.
rewrite cEx_ExInd.
rewrite Rsqr_div'.
apply: (@leR_trans (sqrt ((`V X') / (Pr P' good)))).
  apply: sqrt_le_1_alt.
  apply: (@leR_trans ((`E ((X' `-cst mu) `^2) * `E (Ind good `^2))/ Rsqr(Pr P' good))).
  apply leR_pmul2r.
    apply: invR_gt0; apply Rlt_0_sqr. admit.
  exact: Cauchy_Schwarz_proba.
  have -> : `E ((X' `-cst mu) `^2) = `V X'.
    rewrite/Var. admit.
  admit.
Admitted.

Lemma lemma_1_4_1 :
  Pr P bad = eps ->
  eps < eps_max ->
  weight C ->
  invariant C ->
  Rabs (mu - mu_hat) <= sqrt(var * 2 * eps / (2-eps)) + sqrt(var_hat * 2 * eps / (1-eps)).
Proof.
move => HPr_bad eps_le_max WC IC.
have I1C : invariant1 C.
  apply: lemma1_4_start => //.
    under eq_bigr=>i _ do rewrite mulRC.
    apply/RltP; rewrite lt_neqAle eq_sym PC_neq0/=.
    by apply sumr_ge0 => i _; rewrite coqRE mulr_ge0//; apply/RleP; apply (WC _).1.
  by move: eps_le_max; rewrite /eps_max; lra.
apply: (@Rle_trans _ (`|mu - mu_wave| + `|mu_hat - mu_wave|)).
  have -> : mu - mu_hat = (mu - mu_wave) + (mu_wave - mu_hat) by lra.
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)).
  apply Rplus_le_compat_l.
  rewrite Rabs_minus_sym.
  by right.
have ? : 0 <= eps. rewrite -HPr_bad. apply Pr_ge0.
move: eps_le_max; rewrite /eps_max => eps_le_max.
have ? : 0 < \sum_(i in U) P i * C i.
  apply ltR_neqAle; split.
  apply/eqP; rewrite eq_sym; under eq_bigr => i _ do rewrite mulRC; exact: PC_neq0.
  apply sumCi_ge0 => //.
apply: leR_add; rewrite -(geR0_norm _ (sqrt_pos _)); apply Rsqr_le_abs_0; rewrite Rsqr_sqrt.
- apply lemma_1_4_step2 => //.
- repeat apply mulR_ge0; try lra.
  + apply cvariance_nonneg.
  + apply invR_ge0; lra.
- apply lemma_1_4_step1 => //.
  + move=> i; apply (WC i).1.
  + split => //; lra.
- repeat apply mulR_ge0; try lra.
  + apply/RleP; apply sumr_ge0 => i _.
    rewrite !coqRE; apply mulr_ge0.
      by apply mulr_ge0; first apply FDist.ge0; apply/RleP; apply ((WC i).1).
    by apply/RleP; apply sq_RV_ge0.
  + apply invR_ge0 => //.
  + apply invR_ge0; lra.
Qed.

Lemma eqn_a6_a9 :
  16 * var <= var_hat ->
  0 < eps -> eps < eps_max -> 
  weight C ->
  invariant C ->
  Pr P bad = eps ->
  \sum_(i in good) P i * C i * tau i <= 0.25 * (1 - eps) * var_hat.
Proof.
rewrite /eps_max; move => var16 esp_pos eps1_12 WC IC HPr_bad.
have I1C : invariant1 C. (* todo: repeated, factor out *)
  apply: lemma1_4_start => //.
    under eq_bigr=>i _ do rewrite mulRC.
    apply/RltP; rewrite lt_neqAle eq_sym PC_neq0/=.
    by apply sumr_ge0 => i _; rewrite coqRE mulr_ge0//; apply/RleP; apply (WC _).1.
  by move: eps1_12; lra.

have [/psumr_eq0P PiCieq0|?] := eqVneq (\sum_(i in U) P i * C i) 0.
  apply: (@leR_trans 0).
    right; apply/eqP; rewrite psumr_eq0.
      apply/allP => i _; rewrite PiCieq0//; first rewrite mul0R eqxx implybT//.
      by move=> i0 _; rewrite coqRE mulr_ge0//; apply/RleP; apply WC.
    move=>i _. rewrite !coqRE mulr_ge0//; last by apply/RleP; apply tau_ge0.
    by rewrite mulr_ge0//; apply/RleP; apply WC.
    apply: mulR_ge0.
    apply: mulR_ge0. interval. lra.
    apply: (@leR_trans (16 * var)) => //. 
    by apply: mulR_ge0; first lra; apply cvariance_nonneg.
have sumCi_gt0 : 0 < \sum_(i in U) P i * C i.
    apply ltR_neqAle; split.
    - by apply/eqP; rewrite eq_sym.
    - apply/RleP. apply sumr_ge0 => i _. rewrite RmultE mulr_ge0//. apply/RleP. apply WC.
have Hvar_hat_2_eps: 0 <= var_hat * 2 * eps.
  rewrite -mulRA; apply mulR_ge0 => //; last lra.
  rewrite /var_hat.
  by apply var_hat_ge0; first by move => i; apply WC.
have PrPgoodpos : 0 < Pr P good.
  move: HPr_bad; rewrite Pr_of_cplt; by lra.

(*a6*)
apply leR_trans with (y := (1 - eps) * (var + (mu - mu_hat)²)).
  have HPr_good: Pr P good = 1 - eps.
  by rewrite -HPr_bad Pr_of_cplt subRB subRR add0R.
  rewrite -!HPr_good Rmult_comm -leR_pdivr_mulr.
    apply eqn1_1. by exact PrPgoodpos.
    move => a. by auto. 
  by exact PrPgoodpos.

(*a6-a7*)
apply leR_trans with (y :=(1 - eps) * (var + (sqrt(var * 2 * eps / (2-eps)) + sqrt(var_hat * 2 * eps / (1-eps)))²)).
  apply leR_wpmul2l. 
    rewrite -HPr_bad subR_ge0; by exact: Pr_1.
  apply leR_add2l. 
  apply Rsqr_le_abs_1. rewrite [x in _ <= x]geR0_norm.
    apply lemma_1_4_1 => //.
  by apply /addR_ge0/sqrt_pos/sqrt_pos.

(*a7-a8*)
apply leR_trans with (y := (1 - eps) * var_hat * (/16 + 2 * eps * (/(4*sqrt(2-eps)) + /(sqrt(1-eps)))²)).
  rewrite -(mulRA (1-eps)).
  apply leR_pmul2l; first lra.
  rewrite mulRDr.
  apply leR_add; first lra.
  rewrite mulRA mulRA.
  rewrite -(Rsqr_sqrt (var_hat * 2 * eps)); last first.
  auto.
  rewrite -Rsqr_mult mulRDr.
  apply Rsqr_incr_1;
    last (apply addR_ge0; (apply mulR_ge0; first apply sqrt_pos; left; apply invR_gt0; interval));
    last (apply addR_ge0; apply sqrt_pos).
  apply leR_add;
    [rewrite -(sqrt_Rsqr 4); last lra;
    rewrite -sqrt_mult/Rsqr; [|lra|lra]| ];
    rewrite -sqrt_inv -sqrt_mult; try apply: Hvar_hat_2_eps;
    try apply: invR_ge0; try lra.
    apply sqrt_le_1.
    - rewrite /Rdiv -!mulRA; apply mulR_ge0.
        by apply cvariance_nonneg.
      by rewrite mulRA; apply mulR_ge0; [lra|left; apply invR_gt0; lra].
    - apply mulR_ge0; first exact: Hvar_hat_2_eps.
      by [lra|left;apply invR_gt0;lra].
    rewrite invRM; [|apply /eqP;lra|apply /eqP; lra].
    rewrite (mulRC (/ _)) mulRA (mulRC _ (/ _)) mulRA mulRA mulRA /Rdiv -4!mulRA.
    apply leR_pmul; [apply cvariance_nonneg |
        rewrite mulRA; apply mulR_ge0; [lra | left; apply invR_gt0; lra]| | ].
      rewrite mulRC /Rsqr; by lra.
    by right.
  rewrite Rsqr_sqrt; [by right|nra].

(*a8-a9*)
apply leR_trans with (y := (1-eps) * var_hat * (/16 + 2 * eps_max * Rsqr (/(4 * sqrt (2 - eps_max)) + /sqrt(1-eps_max)))).
  rewrite /eps_max.
  apply leR_pmul.
    apply mulR_ge0; first lra.
      by apply var_hat_ge0 => [u|//]; apply WC. 
    apply addR_ge0; first lra. apply mulR_ge0; first lra. by apply Rle_0_sqr. 
    by right.
  apply leR_add.
    by right.
  apply leR_pmul; first lra. 
    by apply Rle_0_sqr.
    by lra.
  apply Rsqr_bounds_le. split.
    by interval.
  apply leR_add.
    apply leR_inv.
      apply mulR_gt0; first lra.
      by apply sqrt_lt_R0; first lra.
    apply leR_wpmul2l; first lra.
    by apply sqrt_le_1; lra.
  apply leR_inv.
    by apply sqrt_lt_R0; lra.
  apply sqrt_le_1; lra.
rewrite mulRC mulRA.
apply leR_wpmul2r => //. apply var_hat_ge0 => [u|//]. apply WC.
apply leR_wpmul2r; first lra.
rewrite /eps_max.
interval.
Qed.

Lemma eqn_a10_a11 :
  16 * var <= var_hat ->
  0 < eps -> eps < eps_max ->
  weight C ->
  invariant C ->
  Pr P bad = eps ->
  2/3 * var_hat <= \sum_(i in bad) P i * C i * tau i.
Proof.
rewrite /eps_max; move => var16 esp_pos eps1_12 HwC HiC HPr_bad.
have var_hat_pos: 0 <= var_hat.
 apply : (leR_trans _ var16).
 apply mulR_ge0; first by lra.
 apply cvariance_nonneg.
have PrPgoodpos : 0 < Pr P good.
  move: HPr_bad; rewrite Pr_of_cplt; lra.

have ->: \sum_(i in bad) P i * C i * tau i =
  var_hat * (\sum_(i in U) P i * C i) - (\sum_(i in good) P i * C i * tau i).
  rewrite /var_hat -mulRA Rinv_l ?mulR1; last first.
    by apply/eqP; under eq_bigr => i _ do rewrite mulRC; exact: PC_neq0.
  rewrite -addR_opp big_morph_oppR big_mkcond [X in _ + X]big_mkcond -big_split/=.
  apply: eq_bigr => i _; rewrite /bad in_setC; symmetry.
  by case: ifP => /= _; rewrite ?addRN ?addR0.
apply (@leR_trans (var_hat * (1-3/2*eps) - \sum_(i in good) P i * C i * tau i)); last first.
  apply/RleP; rewrite !coqRE lerB// ler_pM// ?subr_ge0 -!coqRE; apply/RleP => //; first lra.
  move: (good_mass HPr_bad eps1_12 HwC HiC).
  move/(Rmult_le_compat_r (Pr P good) _ _ (Pr_ge0 _ good)).
  rewrite -Rmult_div_swap Rmult_div_l; last exact: Rgt_not_eq.
  rewrite Pr_to_cplt HPr_bad.
  rewrite Rmult_minus_distr_r Rmult_minus_distr_l mulR1.
  rewrite Rmult_minus_distr_l subRB.
  move/(Rle_trans (1 - 3/2 * eps)) => H.
  apply: (Rle_trans _ _ _ (H _)); first nra.
  apply: leR_sumRl => //.
  move=> i _; exact: Rle_refl.
  move=> i _; apply: Rmult_le_pos.
  - apply/RleP; exact: FDist.ge0.
  - exact: (HwC i).1.

apply (@leR_trans ((1 - 3 / 2 * eps - 0.25 * (1 - eps)) * var_hat)); last first.
  apply/RleP; rewrite !coqRE mulrBl (mulrC var_hat) lerB// -!coqRE; apply/RleP; exact: eqn_a6_a9.

apply (@leR_trans ((1 - 3 / 2 * eps_max - 0.25 * (1 - eps_max)) * var_hat)); last first.
  apply leR_wpmul2r=>//. apply/RleP.
  rewrite -!subRD !coqRE lerB// !mulrBr. 
  rewrite (addrC (_*1)) (addrC (_*1)) !addrA lerD//.
  rewrite -!mulrBl ler_pM// /eps_max.
  - by rewrite -!coqRE; apply/RleP; interval.
  - by rewrite ltW//; apply/RltP.
  - by rewrite ltW//; apply/RltP.

apply leR_wpmul2r => //; interval.
Qed.

(* TODO: improve the notation for pos_ffun (and for pos_fun) *)
Lemma eqn1_3_4 (S: {set U}):
  let C' := update in
  0 < tau_max ->
  \sum_(i in S) P i * (1 - C' i) =
    (\sum_(i in S) P i * (1 - C i)) +
    1 / tau_max * (\sum_(i in S ) P i * (C i * tau i)).
Proof.
move => C' tau_max_gt0.
have <- : \sum_(i in S) P i * (C i - C' i) =
         1 / tau_max * (\sum_(i in S) P i * (C i * tau i)).
  rewrite /C' /update big_distrr.
  apply eq_bigr => i _ /=.
  rewrite /update_ffun ffunE.
  have [->|Ci-] := eqVneq (C i) 0; first by rewrite orbT subRR !(mulR0,mul0R).
  rewrite orbF ifF; last by rewrite (negbTE (gtR_eqF _ _ tau_max_gt0))/=.
  by field; exact/eqP/gtR_eqF.
rewrite -big_split/=.
apply eq_bigr => i HiS.
by rewrite -mulRDr addRA subRK.
Qed.

Lemma lemma_1_5 :
  let C' := update in
  0 < tau_max ->
  \sum_(i in good) P i * (C i * tau i) <=
    (1 - eps) / 2 * (\sum_(i in bad) P i * (C i * tau i)) ->
  invariant C -> invariant C'.
Proof.
rewrite /invariant => tau_max_gt0 H1 IH1.
rewrite !eqn1_3_4 // !mulRDr.
apply leR_add; first exact IH1.
rewrite (mulRC ((1 - eps) / 2)) -mulRA.
apply leR_pmul2l; first by rewrite /Rdiv mul1R; apply invR_gt0.
by rewrite mulRC; exact H1.
Qed.

End lemma_1_4.

Section filter1d.
Variables (U : finType) (P : {fdist U}).
Variable X : {RV P -> R}.
Variable good : {set U}.

(* TODO: split file here? *)
Require Import Program.Wf.

Local Obligation Tactic := idtac.
Program Fixpoint filter1d (C : nneg_finfun U ) (HC : Weighted.total P C != 0)
    {measure #| 0.-support (tau X HC)| } :=
  match Bool.bool_dec (Weighted.total P C != 0) true with
  | right _ =>  None
  | left H =>
  match #| 0.-support (tau X H) | with
  | 0      => None
  | S gas' => if Rleb (var_hat X H) (var X good)
              then Some (mu_hat X H)
              else filter1d (update_valid_weight X HC)
  end
end.
Next Obligation.
move=> /= C HC _ H _ n Hn.
move: (ltn0Sn n); rewrite Hn => /card_gt0P [] u; rewrite supportE.
move: (tau_ge0 X H u)=> /[swap] /eqP /nesym /[conj] /ltR_neqAle Hu.
(*
set stuC := 0.-support (tau (update C)).
set stC := 0.-support (tau C).
have stuC_stC: stuC \subset stC by admit.
have max_notin_sutC: arg_tau_max C \notin stuC.
- rewrite supportE; apply/negPn.
  rewrite /tau /trans_min_RV sq_RV_pow2; apply/eqP/mulR_eq0; left.
  rewrite /mu_hat.
  rewrite /update.
*)
(*
have max_in_stC: arg_tau_max C \in stC.
- rewrite supportE.
  apply/eqP/nesym; apply ltR_neqAle.
  by apply/(ltR_leR_trans Hu)/RleP/arg_rmax2_cond.
suff: stuC \proper stC by move/proper_card/leP.
apply/properP; split => //.
by exists (arg_tau_max C).
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

(*
Lemma first_note (C: {ffun U -> R}):
  invariant C -> 1 - eps <= (\sum_(i in good) C i * P i) / (\sum_(i in U) C i * P i).
Admitted.
*)
End filter1d.
