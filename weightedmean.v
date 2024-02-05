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

(* TODO: move, inspired by mathcomp analysis *)
Lemma setT_bool : [set: bool] = [set true; false].
Proof.
apply/eqP; rewrite eqEsubset; apply/andP; split => //.
by apply/subsetP => x; rewrite !inE; case: x.
Qed.

Module Split.
Section def.
Variables (A : finType) (d0 : {fdist A}) (c : nneg_finfun A).
Definition g := fun x => if x.2 then c x.1 else (1 - c x.1).
Hypothesis weight_C : forall i, 0 <= c i <= 1.
Definition f := [ffun x => g x * d0 x.1].

Lemma g_ge0 x : (0 <= g x)%mcR.
Proof.
rewrite/g.
case: ifPn => _.
by case: c => c' /= /forallP.
have [_ ?] := weight_C x.1.
by apply/RleP; apply subR_ge0.
Qed.

Lemma f0 a : (0 <= f a)%mcR.
Proof.
rewrite ffunE /f coqRE.
rewrite mulr_ge0 => //.
exact: g_ge0.
Qed.

Lemma f1 : \sum_a f a = 1.
Proof.
transitivity (\sum_(x in ([set: A] `* setT)%SET) f x).
  by apply: eq_bigl => /= -[a b]; rewrite !inE.
rewrite big_setX/=.
rewrite exchange_big//= setT_bool.
rewrite big_setU1//= ?inE// big_set1//=.
rewrite -big_split//=.
rewrite -(Pr_setT d0).
rewrite /Pr/=.
apply: eq_bigr => a _.
rewrite !ffunE/g/=.
lra.
Qed.

Definition d : {fdist _} := locked (FDist.make f0 f1).
Lemma dE a : d a = (if a.2 then c a.1 else (1 - c a.1)) * d0 a.1.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.

Definition X'' (X : {RV d0 -> R}) : {RV d -> R} := fun x => X x.1.

Lemma H1 good : Pr d0 good = Pr d (good `* [set: bool]).
Proof.
rewrite /Pr big_setX/=.
apply: eq_bigr => u ugood.
rewrite setT_bool big_setU1//= ?inE// big_set1.
rewrite !dE/=.
by rewrite -mulRDl addRCA addR_opp subRR addR0 mul1R.
Qed.

Lemma cEx (X : {RV d0 -> R}) good :
  `E_[X | good] = `E_[X'' X | (good `* [set: bool])].
Proof.
rewrite !cExE; congr (_ / _); last exact: H1.
rewrite big_setX//=; apply: eq_bigr => u ugood.
rewrite setT_bool big_setU1//= ?inE// big_set1.
rewrite !dE/= /X''/=.
rewrite -mulRDr -mulRDl addRCA addR_opp.
by rewrite subRR addR0 mul1R.
Qed.

End def.
Section prop.
Variables (A : finType) (d0 : {fdist A}) (p : prob R)  (c : nneg_finfun A).
End prop.
End Split.

(*
Variable (A : finType) (d0 : {fdist A}) (c : pos_ffun A) (ax : WeightedFDist.axiom d0 c).
Definition wd := WeightedFDist.d ax.
!!!!!
*)


Section lemma_1_4.
Variables (U : finType) (P : {fdist U}).
Variable X : {RV P -> R}.
 
Definition weight (C : {ffun U -> R}) :=
  (forall i, 0 <= C i <= 1).

Variable C : nneg_finfun U.
Hypothesis weight_C : weight C.
Hypothesis PC_neq0 : Weighted.total P C != 0.
Let P' := Weighted.d PC_neq0.
Let P'' := Split.d P weight_C.

Variable good : {set U}.
Definition bad := ~: good.

Variable eps : R.
Definition eps_max := 1/16.

Hypothesis pr_bad : Pr P bad = eps.
Hypothesis low_eps : eps <= eps_max.
Let eps0 : 0 <= eps.
Proof. rewrite -pr_bad. exact: Pr_ge0. Qed.

Definition C0 : {ffun U -> R} := [ffun=> 1]. (*Definition C0 (i: U) := 1. *)
Lemma C0' : (forall u, 0 <= C u) -> [forall a, 0 <= C a]%mcR.
Proof. by move=> h; apply/forallP => u; apply/RleP. Qed.
Definition Cpos_fun h := mkNNFinfun (C0' h).

Definition X' : {RV P' -> R} := X.

Definition mu := `E_[X | good].
Definition mu_hat := `E X'.
Definition mu_wave := `E_[X' | good].
(* was  (\sum_(i in good) P i * C i * X i) / (\sum_(i in good) P i * C i). *)

Definition var := `V_[X | good].
Definition var_hat := `V X'.
(* was (\sum_(i in U) P i * C i * tau i) / (\sum_(i in U) P i * C i).*)
Definition var_wave := `V_[X' | good].

Lemma mu_hatE :
  mu_hat = (\sum_(i in U) C i * P i * X i) / \sum_(i in U) C i * P i.
Proof.
rewrite /mu_hat /Ex /ambient_dist divRE.
rewrite big_distrl/=; apply: eq_bigr => u _.
rewrite -mulRA mulRCA; congr (_ * _).
by rewrite /P' Weighted.dE (mulRC _ (P u)) -divRE; congr (_ / _).
Qed.

Definition tau := (X `-cst mu_hat)`^2.
Lemma tau_ge0 i : 0 <= tau i.
Proof. rewrite /tau sq_RV_pow2; exact: pow2_ge_0. Qed.

Definition tau_max := \rmax_(i in [set: U] | C i != 0) tau i.
Lemma tau_max_ge0 : 0 <= tau_max.
Proof. rewrite /tau_max -big_filter; apply bigmaxR_ge0=> *; exact:tau_ge0. Qed.

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

Lemma eqn1_1 :
  0 < Pr P good ->
 (\sum_(i in good) C i * P i * tau i) / Pr P good <= var + (mu - mu_hat)².
Proof.
move => HPgood.
apply leR_trans with (y := `E_[tau | good]);
  last by apply/leR_eqVlt;left;apply/cVarDist.
rewrite cExE.
apply leR_pmul2r; [by apply invR_gt0|].
apply leR_sumRl => i Higood; last by [].
  rewrite (mulRC (tau i)).
  apply leR_wpmul2r; first apply tau_ge0.
  have [_ c1] := weight_C i.
  have /RleP hp := FDist.ge0 P i.
  by rewrite -{2}(mul1R (P i)); apply leR_wpmul2r.
by apply mulR_ge0 => //; apply tau_ge0.
Qed.

Definition invariant :=
  (\sum_(i in good) (1 - C i) * P i <= (1 - eps) / 2 * \sum_(i in bad) (1 - C i) * P i).
Definition invariant1 :=
  (1 - eps <= Pr P' good).

Let pr_good : Pr P good = 1 - eps.
Proof. by rewrite Pr_to_cplt pr_bad. Qed.

Lemma lemma1_4_start :
  0 < \sum_(i in U) C i * P i ->
  invariant -> invariant1.
Proof.
rewrite /weight/invariant/invariant1 => HCi_gt0 hinv.
rewrite -!pr_good.
apply leR_trans with (y := (Pr P good / 2 * (1 + Pr P good + (\sum_(i in bad) C i * P i))) / (\sum_(i in U) C i * P i)).
apply leR_pmul2r with (m := (\sum_(i in U) C i * P i) * 2); first by apply mulR_gt0.
rewrite !mulRA !(mulRC _ 2) -(mulRA _ (/ _)) mulVR; last by apply gtR_eqF.
rewrite mulR1 !mulRA (mulRC _ (/2)) mulRA mulVR; last by apply gtR_eqF.
rewrite mul1R -addRR mulRDl -addRA mulRDr.
apply leR_add.
apply leR_pmul2l; first by move: low_eps; rewrite pr_good /eps_max; lra.
rewrite -(Pr_setT P) /Pr.
apply leR_sumRl => i _//; first by rewrite //-{2}(mul1R (P i)); apply leR_wpmul2r; [|apply weight_C].
apply leR_pmul2l; first by move: low_eps; rewrite /eps_max pr_good; lra.
rewrite /Pr addRC -bigID2.
apply leR_sumR => i HiU.
case: ifPn => igood; first by apply Rle_refl.
by rewrite -{2}(mul1R (P i)); apply leR_pmul; try apply weight_C; auto; right.
under [X in _ <= X]eq_bigr do rewrite Weighted.dE /Weighted.total.
rewrite -big_distrl/= divRE.
apply leR_pmul2r; first by apply invR_gt0.
apply Ropp_le_cancel.
rewrite {2}pr_good addRA -addRA -pr_bad mulRDr oppRD addRC.
apply leR_subl_addr.
rewrite /Rminus oppRK -mulRN addRC {1}/Rdiv -mulRA mulVR; last by apply gtR_eqF.
rewrite mulR1 oppRD oppRK !big_morph_oppR-!big_split/=.
have H: forall S, \sum_(i in S) (P i + - (C i * P i)) = \sum_(i in S) (1 - C i) * P i.
  by move => p S; apply eq_bigr => i _; rewrite mulRBl mul1R addR_opp.
by rewrite !H pr_good.
Qed.

Lemma sumCi_ge0 : weight C -> 0 <= \sum_(i in U) C i * P i.
Proof.
move=> Hweight.
by apply/RleP; apply sumr_ge0 => i _;
  rewrite coqRE mulr_ge0//; apply /RleP; apply Hweight.
Qed.

Lemma h1 h : Weighted.total P (Cpos_fun h) != 0.
Proof.
move: PC_neq0.
rewrite /Weighted.total.
by under eq_bigr do rewrite mulRC.
Qed.

Lemma lemma_1_4_step1 :
  0 < \sum_(i in U) C i * P i (* NB: this can be proved from the termination condition *) ->
  Pr P' good != 0 ->
  invariant1 ->
  Rsqr (mu_hat - mu_wave) <= var_hat * 2 * eps / (1 - eps).
Proof.
move=> PC0 pgoodC invC.
unfold eps_max in low_eps.
suff h : `| mu_hat - mu_wave | <= sqrt (var_hat * 2 * eps / (1 - eps)).
  rewrite Rsqr_abs -[X in _ <= X]Rsqr_sqrt; last first.
    apply: mulR_ge0; last by apply/invR_ge0/subR_gt0; lra.
    by repeat apply: mulR_ge0; [exact: variance_nonneg|lra|rewrite -pr_bad; exact: Pr_ge0].
  by apply/Rsqr_incr_1 => //; [exact/normR_ge0|exact: sqrt_pos].
pose delta := 1 - eps.
have {1}-> : eps = 1 - delta by rewrite subRB subRR add0R.
rewrite -/delta distRC.
rewrite /mu_hat.
by apply: resilience => //; rewrite /delta; lra.
Qed.

Lemma good_mass : 
  invariant ->
  1 - eps/2 <= (\sum_(i in good) C i * P i) / Pr P good.
Proof.
rewrite /eps_max/weight => Hinv.
unfold eps_max in low_eps.
apply leR_trans with (y := 1 - (1-eps)/2/Pr P good * Pr P bad).
  by rewrite pr_bad pr_good -!mulRA mulRC (mulRC (/(_-_))) mulRA -mulRA mulVR; [rewrite mulR1 mulRC; right|apply /gtR_eqF; lra].
apply leR_trans with (y := 1 - (1-eps)/2/Pr P good * \sum_(i in bad) P i * (1 - C i)).
  rewrite leR_add2l leR_oppl oppRK leR_pmul2l;
    last (rewrite pr_good /Rdiv mulRC mulRA mulVR; [lra|rewrite gt_eqF//; apply/RltP; lra]).
  apply leR_sumR => i Hi_bad.
  rewrite -{2}(mulR1 (P i)).
  move: (FDist.ge0 P i); move/RleP => [HPi_gt0|HPi_eq0].
    by apply/RleP; rewrite !coqRE ler_wpM2l// gerBl//; move: (weight_C i).1 => /RleP.
  by rewrite -HPi_eq0 !mul0R.
rewrite -pr_good /Rdiv -(mulRA (Pr P good)) (mulRC (/2)) mulRA mulRV; last by (apply gtR_eqF; lra).
apply leR_pmul2r with (m := Pr P good);
  [rewrite pr_good; lra|rewrite -(mulRA _ (/ Pr P good)) mulVR; [rewrite mul1R mulR1|apply gtR_eqF; lra]].
rewrite mulRDl mul1R {2}pr_good mulRC mulRN.
apply Rplus_le_reg_l with (r := -Pr P good).
rewrite addRA (addRC (- _)) addRN add0R mulRA.
apply leR_oppl.
rewrite oppRD oppRK /Pr -(mul1R (- _)) mulRN -mulNR big_distrr -big_split -divRE/=.
under eq_bigr => i _ do rewrite mulNR mul1R -{1}(mul1R (P i)) -mulNR -Rmult_plus_distr_r addR_opp.
under [X in _ <= _ / _ * X]eq_bigr => i _ do rewrite mulRC.
by [].
Qed.

Let X'' := Split.X'' weight_C X.

Lemma lemma_1_4_step2 :
  invariant ->
  Rsqr (mu - mu_wave) <= var * 2*eps / (2-eps).
Proof.
move=> Hinv.
unfold eps_max in low_eps.
have -> : mu = `E_[X'' | good `* [set: bool]].
  rewrite /mu.
  exact: Split.cEx.
have -> : mu_wave = `E_[X'' | good `* [set true]].
  rewrite /mu_wave !cExE !divRE !big_distrl/= big_setX//=.
  rewrite /Pr big_setX//=; apply: eq_bigr => u ugood.
  rewrite big_set1 /P'/P''.
  rewrite /X' /X'' /Split.X'' /=.
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
apply: (@leR_trans (`V_[ X'' | good `* [set: bool]] * 2 * (1 - (1 - eps / 2)%mcR) / (1 - eps / 2)%mcR)).
  apply: sqrt_le_0.
  - exact: Rle_0_sqr.
  - apply: mulR_ge0.
    + apply: mulR_ge0.
      * apply: mulR_ge0.
        - exact: cvariance_nonneg.
        - lra.
      * rewrite -!coqRE.
        rewrite subRB subRR add0R.
        apply: divR_ge0 => //.
    + apply: invR_ge0; rewrite -!coqRE (_ : 2%:R = 2)//.
      lra.
  rewrite sqrt_Rsqr_abs.
  apply: (cresilience (delta := 1 - eps / 2)).
  - rewrite -!coqRE; interval.
  - have := good_mass Hinv.
    rewrite -!coqRE.
    move=> /leR_trans; apply.
    apply/leR_eqVlt; left.
    rewrite /Pr !big_setX/=.
    under [X in _ = X * _]eq_bigr do rewrite big_set1.
    congr (_ / _).
      apply: eq_bigr => u ugood.
      by rewrite /P'' Split.dE/= mulRC.
    apply: eq_bigr => u ugood.
    rewrite setT_bool big_setU1//= ?inE// big_set1.
    rewrite /P'' !Split.dE/=.
    by rewrite -mulRDl addRCA addR_opp subRR addR0 mul1R.
  - rewrite /Pr.
  - apply leR_sumRl => i; rewrite inE => /andP[igood _].
    + by right.
    + rewrite Split.dE; apply mulR_ge0 => //.
      by case: ifPn => _; move: (weight_C i.1) => [c0 c1]//; apply subR_ge0.
    + by rewrite inE igood in_setT.
  - apply/subsetP => x.
    by rewrite !inE => /andP[->].
have -> : `V_[ X'' | good `* [set: bool]] = var.
  rewrite /var.
  rewrite /cVar.
  have -> : `E_[X'' | (good `* [set: bool])] = `E_[X | good].
    apply/esym.
    exact: Split.cEx.
  apply/esym.
  exact: Split.cEx.
rewrite !divRE -(mulRA _ eps) -(mulRA _ (1 - _)).
apply leR_wpmul2l.
  apply mulR_ge0; [apply cvariance_nonneg|lra].
rewrite -!coqRE subRB subRR add0R.
rewrite -!divRE -Rdiv_mult_distr Rmult_minus_distr_l mulR1.
rewrite Rmult_div_assoc (mulRC 2) -Rmult_div_assoc divRR ?mulR1.
  rewrite (_ : 2%:R = 2)//.
  exact: Rle_refl.
by apply/eqP; lra.
Qed.

Lemma lemma_1_4_1 :
  invariant ->
  Rabs (mu - mu_hat) <= sqrt(var * 2 * eps / (2-eps)) + sqrt(var_hat * 2 * eps / (1-eps)).
Proof.
move=> IC.
unfold eps_max in low_eps.
have I1C : invariant1.
  apply: lemma1_4_start => //.
    apply/RltP; rewrite lt_neqAle eq_sym PC_neq0/=.
    by apply sumr_ge0 => i _; rewrite coqRE mulr_ge0//; apply/RleP; apply (weight_C _).1.
apply: (@Rle_trans _ (`|mu - mu_wave| + `|mu_hat - mu_wave|)).
  have -> : mu - mu_hat = (mu - mu_wave) + (mu_wave - mu_hat) by lra.
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)).
  apply Rplus_le_compat_l.
  rewrite Rabs_minus_sym.
  by right.
have ? : 0 <= eps by rewrite -pr_bad; apply Pr_ge0.
have ? : 0 < \sum_(i in U) C i * P i.
  apply ltR_neqAle; split.
  by apply/eqP; rewrite eq_sym; apply PC_neq0.
  apply sumCi_ge0 => //.
apply: leR_add; rewrite -(geR0_norm _ (sqrt_pos _)); apply Rsqr_le_abs_0; rewrite Rsqr_sqrt.
- apply lemma_1_4_step2 => //.
- repeat apply mulR_ge0; try lra.
  + apply cvariance_nonneg.
  + apply invR_ge0; lra.
- apply lemma_1_4_step1 => //.
  + by rewrite /invariant1 in I1C; apply/eqP; lra.
- repeat apply mulR_ge0; try lra.
  + apply variance_nonneg. 
  + apply invR_ge0; lra.
Qed.

Lemma eqn_a6_a9 :
  16 * var <= var_hat ->
  invariant ->
  \sum_(i in good) C i * P i * tau i <= 0.25 * (1 - eps) * var_hat.
Proof.
rewrite /eps_max; move => var16 IC.
unfold eps_max in low_eps.
have I1C : invariant1. (* todo: repeated, factor out *)
  apply: lemma1_4_start => //.
    apply/RltP; rewrite lt_neqAle eq_sym PC_neq0/=.
    by apply sumr_ge0 => i _; rewrite coqRE mulr_ge0//; apply/RleP; apply (weight_C _).1.
have [/psumr_eq0P PiCieq0|?] := eqVneq (\sum_(i in U) C i * P i) 0.
  apply: (@leR_trans 0).
    right; apply/eqP; rewrite psumr_eq0.
      apply/allP => i _; rewrite PiCieq0//; first rewrite mul0R eqxx implybT//.
      by move=> i0 _; rewrite coqRE mulr_ge0//; apply/RleP; apply weight_C.
    move=>i _. rewrite !coqRE mulr_ge0//; last by apply/RleP; apply tau_ge0.
    by rewrite mulr_ge0//; apply/RleP; apply weight_C.
    apply: mulR_ge0.
    apply: mulR_ge0. interval. lra.
    apply: (@leR_trans (16 * var)) => //. 
    by apply: mulR_ge0; first lra; apply cvariance_nonneg.
have sumCi_gt0 : 0 < \sum_(i in U) C i * P i.
    apply ltR_neqAle; split.
    - by apply/eqP; rewrite eq_sym.
    - apply/RleP. apply sumr_ge0 => i _. rewrite RmultE mulr_ge0//. apply/RleP. apply weight_C.
have Hvar_hat_2_eps: 0 <= var_hat * 2 * eps.
  by rewrite -mulRA -pr_bad; repeat apply mulR_ge0; [apply variance_nonneg|lra|exact: Pr_ge0].
  rewrite /var_hat.
have PrPgoodpos : 0 < Pr P good.
  move: pr_bad; rewrite Pr_of_cplt; by lra.

(*a6*)
apply leR_trans with (y := (1 - eps) * (var + (mu - mu_hat)²)).
  by rewrite -!pr_good Rmult_comm -leR_pdivr_mulr//; apply eqn1_1 => //.

(*a6-a7*)
apply leR_trans with (y :=(1 - eps) * (var + (sqrt(var * 2 * eps / (2-eps)) + sqrt(var_hat * 2 * eps / (1-eps)))²)).
  apply leR_wpmul2l. 
    rewrite -pr_bad subR_ge0; by exact: Pr_1.
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
    - rewrite /Rdiv -!mulRA; apply mulR_ge0; first by apply cvariance_nonneg.
      by repeat apply mulR_ge0; [lra|rewrite -pr_bad; apply Pr_ge0|apply invR_ge0; lra].
    - apply mulR_ge0; first exact: Hvar_hat_2_eps.
      by [lra|left;apply invR_gt0;lra].
    rewrite invRM; [|apply /eqP;lra|apply /eqP; lra].
    rewrite (mulRC (/ _)) mulRA (mulRC _ (/ _)) mulRA mulRA mulRA /Rdiv -4!mulRA.
    apply leR_pmul.
    - apply cvariance_nonneg.
    - repeat apply mulR_ge0; [lra |rewrite-pr_bad; apply Pr_ge0|apply invR_ge0; lra].
    - rewrite mulRC /Rsqr; by lra.
    by right.
  rewrite Rsqr_sqrt; [by right|nra].

(*a8-a9*)
apply leR_trans with (y := (1-eps) * var_hat * (/16 + 2 * eps_max * Rsqr (/(4 * sqrt (2 - eps_max)) + /sqrt(1-eps_max)))).
  rewrite /eps_max.
  apply leR_pmul.
    apply mulR_ge0; first lra.
      by apply variance_nonneg.
    apply addR_ge0; first lra. 
    repeat apply mulR_ge0;[lra|rewrite -pr_bad; apply Pr_ge0| |].
    apply addR_ge0; apply invR_ge0; first apply mulR_gt0; try lra; apply sqrt_lt_R0; lra.
    apply addR_ge0; apply invR_ge0; first apply mulR_gt0; try lra; apply sqrt_lt_R0; lra.
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
apply leR_wpmul2r => //. exact: variance_nonneg.
apply leR_wpmul2r; first lra.
rewrite /eps_max.
interval.
Qed.

Lemma eqn_a10_a11 :
  16 * var <= var_hat ->
  0 < \sum_(i in U) C i * P i ->
  invariant ->
  2/3 * var_hat <= \sum_(i in bad) C i * P i * tau i.
Proof.
rewrite /eps_max; move => var16 sumCi_pos HiC.
unfold eps_max in low_eps.
have PrPgoodpos : 0 < Pr P good by rewrite pr_good; lra.

have ->: \sum_(i in bad) C i * P i * tau i =
  var_hat * (\sum_(i in U) C i * P i) - (\sum_(i in good) C i * P i * tau i).
  rewrite /var_hat /Var{1}/Ex.
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
  rewrite /tau/mu_hat /P' Weighted.dE.
  rewrite mulRC {2}/X' -mulRA; congr (_ * _).
  rewrite /Weighted.total -mulRA Rinv_l ?mulR1//.
  exact: Rgt_not_eq.

apply (@leR_trans (var_hat * (1-3/2*eps) - \sum_(i in good) C i * P i * tau i)); last first.
  rewrite -!addR_opp; apply: Rplus_le_compat_r.
  apply leR_wpmul2l; first exact: variance_nonneg.
  apply: (@leR_trans ((1 - eps / 2) * (1 - eps))); first nra.
  apply: leR_trans.
  move: (good_mass HiC).
  move/(Rmult_le_compat_r (Pr P good) _ _ (Pr_ge0 _ good)).
  rewrite -Rmult_div_swap Rmult_div_l; last exact: Rgt_not_eq.
  rewrite Pr_to_cplt pr_bad; apply.
  apply leR_sumRl => //i igood.
  + by right.
  + by apply mulR_ge0 => //; apply (weight_C _).1.

apply (@leR_trans ((1 - 3 / 2 * eps - 0.25 * (1 - eps)) * var_hat)); last first.
  rewrite mulRBl (mulRC var_hat). 
  apply: leR_add; last by apply Ropp_le_contravar; exact: eqn_a6_a9.
  apply leR_wpmul2r; first exact: variance_nonneg.
  by right.

apply (@leR_trans ((1 - 3 / 2 * eps_max - 0.25 * (1 - eps_max)) * var_hat)); last first.
  apply leR_wpmul2r; first apply variance_nonneg.
  rewrite /eps_max. nra.
by rewrite/eps_max; apply leR_wpmul2r; first apply variance_nonneg; nra.
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

End lemma_1_4.

Section lemma_1_5.
(* cleanup here *)
Variables (U : finType) (P : {fdist U}).
Variable X : {RV P -> R}.

Variable C : nneg_finfun U.
Variable good : {set U}.

Variable eps : R.

Lemma lemma_1_5 :
  let C' := update in
  0 < (tau_max X (h1 _ _)) ->
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

End lemma_1_5.


Section base_case.
(* TODO: define a proper environment *)
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
End base_case.

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
