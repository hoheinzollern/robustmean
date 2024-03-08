From mathcomp Require Import all_ssreflect ssralg ssrnum matrix.
From mathcomp Require boolp.
From mathcomp Require Import Rstruct reals mathcomp_extra.
From mathcomp Require Import lra.
Require Import Reals.
From infotheo Require Import ssrR Reals_ext realType_ext logb ssr_ext ssralg_ext.
From infotheo Require Import bigop_ext fdist proba.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*Local Open Scope R_scope.*)
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
(* |        is01 C | := | forall i, 0 <= C i <= 1                             *)
(* |    Weighted.d | == | given a distribution $d0$ and a non-negative        *)
(* |               |    | function $g$, returns the distribution              *)
(* |               |    | $a\mapsto \frac{g(a) * d0(a)}{\sum_b g(b) * d0(b)}$ *)
(* |       Split.d | == | given a distribution $d0$ and a non-negative        *)
(* |               |    | function $h$, returns the distribution              *)
(* |               |    | $\begin{array}{rl} (a,b) \mapsto & h(a) * d0(a) \textrm{ if } b \\ & (1 - h(a))*d0(a) \textrm{ o.w.}\end{array}$ *)
(* |      sq_dev X | == | "squared deviation": $(X - mean)^2$                 *)
(* |    emean_cond | == | mean of the at least $1 - \varepsilon$ fraction     *)
(* |               |    | (under c) of the points in $S$                      *)
(* |         emean | == | empirical/estimate mean of the data,                *)
(* |               |    | weighted mean of all the points                     *)
(* |               |    | (defined using emean_cond)                          *)
(* |     evar_cond | == | `V_[X : {RV (Weighted.d PC0) -> R} | A]              *)
(* |          evar | == | empirical variance                                  *)
(* |     invariant | == | the amount of mass removed from the points in $S$   *)
(* |               |    | is smaller than that removed from the points in $\bar S$ *)
(* | filter1D_invW | == | the amount of mass attached to the points in $S$ is *)
(* |               |    | at least $1 - \varepsilon$                          *)
(* |      filter1D | == | robust mean estimation by comparing mean and        *)
(* |               |    | variance                                            *)
(*                                                                            *)
(******************************************************************************)

Section is01.
Local Open Scope ring_scope.
Definition is01 (U : finType) (C : {ffun U -> R}) := forall i, 0 <= C i <= 1.
End is01.

Section misc20240303.
Local Open Scope ring_scope.

(* to ssrR *)
Lemma RsqrtE' (x : RbaseSymbolsImpl.R) : sqrt x = Num.sqrt x.
Proof.
set Rx := Rcase_abs x.
have RxE: Rx = Rcase_abs x by [].
rewrite /sqrt.
rewrite -RxE.
move: RxE.
case: Rcase_abs=> x0 RxE.
  by rewrite RxE; have/RltP/ltW/ler0_sqrtr-> := x0.
rewrite /Rx -/(sqrt _) RsqrtE //.
by have/Rge_le/RleP:= x0.
Qed.

(* until we use ring_scope in infotheo *)
Lemma Pr_to_cplt' (A : finType) (P : {fdist A}) (E : {set A}) :  Pr P E = 1 - Pr P (~: E).
Proof. by rewrite Pr_to_cplt !coqRE. Qed.

(* to ssrnum? *)
Lemma sqrBC (R : realDomainType) (x y : R) : (x - y) ^+ 2 = (y - x) ^+ 2.
Proof.
have:= num_real (x - y) => /real_normK <-.
by rewrite distrC real_normK // num_real.
Qed.

(* to ssrnum? *)
Lemma ler_abs_sqr (T : realDomainType) (x y : T) : (`|x| <= `|y|) = (x ^+ 2 <= y ^+ 2).
Proof. by rewrite -ler_sqr ?nomr_nneg // !real_normK ?num_real. Qed.

(* TODO: use ring_scope in robustmean.v *)
Lemma cresilience'
  (V : finType) (PP : {fdist V}) (delta : R) (XX : {RV (PP) -> (R)}) (F G : {set V}) :
  0 < delta -> delta <= Pr PP F / Pr PP G -> F \subset G ->
  `| `E_[XX | F] - `E_[XX | G] | <= Num.sqrt (`V_[ XX | G] * 2 * (1 - delta) / delta).
Proof.
rewrite -!coqRE -RsqrtE' => /RltP ? /RleP ? ?.
exact/RleP/cresilience.
Qed.

Lemma variance_ge0' (U : finType) (P : {fdist U}) (X : {RV (P) -> (R)}) :
  0 <= `V X.
Proof. exact/RleP/variance_ge0. Qed.

Lemma cvariance_ge0' (U : finType) (P : {fdist U}) (X : {RV (P) -> (R)}) (F : {set U}) :
  0 <= `V_[ X | F].
Proof. exact/RleP/cvariance_ge0. Qed.

Lemma resilience'
  (U : finType) (P : {fdist U}) (delta : R) (X : {RV (P) -> (R)}) (F : {set U}) :
  0 < delta -> delta <= Pr P F ->
  `| `E_[X | F] - `E X | <= Num.sqrt (`V X * 2 * (1 - delta) / delta).
Proof.
rewrite -!coqRE -RsqrtE' => /RltP ? /RleP ?.
exact/RleP/resilience.
Qed.

(* analog of ssrR.(pmulR_lgt0', pmulR_rgt0') *)
Lemma wpmulr_lgt0 (R : numDomainType) (x y : R) : 0 <= x -> 0 < y * x -> 0 < y.
Proof.
rewrite le_eqVlt=> /orP [/eqP <- |].
  by rewrite mulr0 ltxx.
by move/pmulr_lgt0->.
Qed.
Lemma wpmulr_rgt0 (R : numDomainType) (x y : R) : 0 <= x -> 0 < x * y -> 0 < y.
Proof. rewrite mulrC; exact: wpmulr_lgt0. Qed.

(* eqType version of order.bigmax_le *)
Lemma bigmax_le' (disp : unit) (T : porderType disp) (I : eqType) (r : seq I) (f : I -> T)
    (x0 x : T) (PP : pred I) :
  (x0 <= x)%O ->
  (forall i : I, i \in r -> PP i -> (f i <= x)%O) ->
  (\big[Order.max/x0]_(i <- r | PP i) f i <= x)%O.
Proof.
move=> x0x cond; rewrite big_seq_cond bigmax_le // => ? /andP [? ?]; exact: cond.
Qed.

(* seq version of order.bigmax_leP *)
Lemma bigmax_leP_seq (disp : unit) (T : orderType disp) (I : eqType) (r : seq I) (F : I -> T)
    (x m : T) (PP : pred I) :
reflect ((x <= m)%O /\ (forall i : I, i \in r -> PP i -> (F i <= m)%O))
  (\big[Order.max/x]_(i <- r | PP i) F i <= m)%O.
Proof.
apply:(iffP idP); last by case; exact:bigmax_le'.
move=> bm; split; first by exact/(le_trans _ bm)/bigmax_ge_id.
by move=> *; exact/(le_trans _ bm)/le_bigmax_seq.
Qed.

Section topology_ext.
Import boolp.
(* variant of robustmean.bigmaxR_ge0_cond, should be moved to topology.v *)
Lemma bigmax_gt0_seq (A : eqType) (F : A -> R) (s : seq A) (PP : pred A) :
reflect (exists i : A, [/\ i \in s, PP i & 0 < F i]) (0 < \big[Num.max/0]_(m <- s | PP m) F m).
Proof.
rewrite ltNge.
apply:(iffP idP).
  move=> /bigmax_leP_seq /not_andP []; first by rewrite lexx.
  move=> /existsNP [] x /not_implyP [] xs /not_implyP [] PPx /negP; rewrite -ltNge=> Fx0.
  by exists x; repeat (split=> //).
case=> x [] ? ? ?; apply/bigmax_leP_seq/not_andP; right.
apply/existsNP; exists x; do 2 (apply/not_implyP; split=> //).
by apply/negP; rewrite -ltNge.
Qed.
End topology_ext.

End misc20240303.

Section proba_ext.
Local Open Scope ring_scope.
Variables (A : finType) (P : {fdist A}).
Lemma Pr_setT' : Pr P [set: A] = 1.
Proof. by rewrite /Pr (eq_bigl xpredT) ?FDist.f1 // => ?; rewrite in_setT. Qed.
End proba_ext.

Section finset_ext.
Variables (R : Type) (idx : R) (op : Monoid.com_law idx) (I : finType) (a b : I) (F : I -> R).
Lemma big_set2 : a != b -> \big[op/idx]_(i in [set a; b]) F i = op (F a) (F b).
Proof. by move=> ab; rewrite big_setU1 ?inE // big_set1. Qed.
End finset_ext.

Module Weighted.
Section def.
Local Open Scope ring_scope.

Variables (A : finType) (d0 : {fdist A}) (g : nneg_finfun A).

Definition total := \sum_(a in A) g a * d0 a.

Hypothesis total_neq0 : total != 0.

Definition f := [ffun a => g a * d0 a / total].

Lemma total_gt0 : 0 < total.
Proof.
rewrite lt_neqAle eq_sym total_neq0/= /total sumr_ge0// => i _.
by apply/mulr_ge0/FDist.ge0; case: g => ? /= /forallP.
Qed.

Lemma total_le1 : (forall i, i \in A -> g i <= 1) -> total <= 1.
Proof.
move=> g1; rewrite -(FDist.f1 d0); apply: ler_sum=> i /(g1 _) g1'.
have:= FDist.ge0 d0 i; rewrite le_eqVlt => /orP [/eqP <- /[!mulr0] // | ?].
by rewrite -[leRHS]mul1r ler_pM2r.
Qed.

Lemma total_le1' : is01 g -> total <= 1.
Proof. by move=> g01; apply: total_le1=> i _; have /andP [] := g01 i. Qed.

Let f0 a : 0 <= f a.
Proof.
rewrite ffunE /f divr_ge0//; last exact/ltW/total_gt0.
by rewrite mulr_ge0 //; case: g => ? /= /forallP; exact.
Qed.

Let f1 : \sum_(a in A) f a = 1.
Proof.
rewrite /f; under eq_bigr do rewrite ffunE.
by rewrite -big_distrl /= mulrV.
Qed.

Definition d : {fdist A} := locked (FDist.make f0 f1).

Lemma dE a : d a = g a * d0 a / total.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.

Lemma support_nonempty : {i | g i != 0}.
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

Definition resample {R : realType} (T : finType) (P Q : {fdist T})
  (X : {RV P -> R}) : {RV Q -> R} := X.
End Weighted.

Notation wgt := Weighted.d.
Notation "Q .-RV X" := (Weighted.resample Q X)
  (at level 10, format "Q .-RV  X") : type_scope.

Module Split.
Section def.
Local Open Scope ring_scope.

Variables (T : finType) (P : {fdist T}) (h : nneg_finfun T).
Hypothesis h01 : is01 h.

Definition g := fun x => if x.2 then h x.1 else 1 - h x.1.

Definition f := [ffun x => g x * P x.1].

Lemma g_ge0 x : (0 <= g x)%mcR.
Proof.
rewrite /g; case: ifPn => _; first by case: h => ? /= /forallP.
by have /andP [_ ?] := h01 x.1; rewrite subr_ge0.
Qed.

Let f0 a : (0 <= f a)%mcR.
Proof. by rewrite ffunE /f mulr_ge0 //; exact: g_ge0. Qed.

Let f1 : \sum_a f a = 1.
Proof.
rewrite /f.
transitivity (\sum_(x in ([set: T] `* setT)%SET) f x).
  by apply: eq_bigl => /= -[a b]; rewrite !inE.
rewrite big_setX /=.
under eq_bigr=> *.
  rewrite setT_bool big_set2 // /f 2!ffunE /g /=.
  rewrite -mulrDl addrCA subrr addr0 mul1r. (* This line is convex.convmm *)
  over.  
under eq_bigl do rewrite inE /=.
by rewrite FDist.f1.
Qed.

Definition d : {fdist T * bool} := locked (FDist.make f0 f1).

Definition fst_RV (X : {RV P -> R}) : {RV d -> R} := X \o fst.

Lemma dE a : d a = (if a.2 then h a.1 else 1 - h a.1) * P a.1.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.

Lemma Pr_setXT A : Pr P A = Pr d (A `* [set: bool]).
Proof.
rewrite /Pr big_setX/=; apply: eq_bigr => u uS.
rewrite setT_bool big_setU1//= ?inE// big_set1.
by rewrite !dE/= -mulRDl addRCA addR_opp subRR addR0 mul1R.
Qed.

Lemma cEx (X : {RV P -> R}) A : `E_[X | A] = `E_[fst_RV X | A `* [set: bool]].
Proof.
rewrite !cExE -Pr_setXT !coqRE; congr (_ / _).
rewrite big_setX//=; apply: eq_bigr => u uS.
rewrite setT_bool big_setU1//= ?inE// big_set1.
rewrite !dE/= /fst_RV/=.
by rewrite -mulRDr -mulRDl addRCA addR_opp subRR addR0 mul1R.
Qed.

Lemma cVar (X : {RV P -> R}) A : `V_[ fst_RV X | A `* [set: bool]] = `V_[X | A].
Proof. by rewrite /cVar/= cEx -[in LHS]cEx. Qed.

End def.
End Split.

Section emean_cond.
Local Open Scope ring_scope.

Context {U : finType} (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U)
  (A : {set U}) (PC0 : Weighted.total P C != 0).

Let WP := Weighted.d PC0.

Hypothesis C01 : is01 C.

Lemma emean_condE :
  `E_[X : {RV WP -> R} | A] = (\sum_(i in A) C i * P i * X i) / (\sum_(i in A) C i * P i).
Proof.
rewrite /Var cExE /Pr /WP !coqRE !sumRE.
under eq_bigr do rewrite Weighted.dE !coqRE mulrA (mulrC (X _)).
rewrite -big_distrl -mulrA; congr (_ * _).
rewrite sumRE -invfM mulrC big_distrl /=.
by under eq_bigr do rewrite Weighted.dE -!mulrA mulVf // mulr1.
Qed.

Lemma emean_cond_split : `E_[X : {RV WP -> R} | A] = `E_[Split.fst_RV C01 X | A `* [set true]].
Proof.
rewrite emean_condE cExE big_setX /= !coqRE; congr (_ / _).
  apply: eq_bigr => u uA.
  by rewrite big_set1 /Split.fst_RV/= Split.dE/= [RHS]mulRC.
by rewrite /Pr big_setX/=; apply: eq_bigr => u uA; rewrite big_set1 Split.dE.
Qed.

End emean_cond.

Section emean.
Local Open Scope ring_scope.

Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U)
  (PC0 : Weighted.total P C != 0).

Let WP := Weighted.d PC0.

(** emean expressed using big sums *)
Lemma emean_sum :
  `E (X : {RV WP -> R}) = (\sum_(i in U) C i * P i * X i) / \sum_(i in U) C i * P i.
Proof.
rewrite /Ex big_distrl/=.
by under eq_bigr do rewrite Weighted.dE mulRCA mulRA.
Qed.

End emean.

Section sq_dev.
Local Open Scope ring_scope.

Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U)
  (PC0 : Weighted.total P C != 0).

Let WP := Weighted.d PC0.
Let X' := X : {RV WP -> R}.

Definition sq_dev := (X `-cst `E X')`^2.

Lemma sq_dev_ge0 u : 0 <= sq_dev u.
Proof. by rewrite /sq_dev sq_RV_pow2; exact/RleP/pow2_ge_0. Qed.

Definition sq_dev_max := \big[Order.max/0]_(i | C i != 0) sq_dev i.

Local Notation j := (sval (Weighted.support_nonempty PC0)).

Definition sq_dev_arg_max := [arg max_(i > j | C i != 0) sq_dev i]%O.

Lemma sq_dev_max_eq_arg : sq_dev_max = sq_dev (sq_dev_arg_max).
Proof.
rewrite /sq_dev_max.
apply: bigmax_eq_arg; first by case: Weighted.support_nonempty.
by move=> *; exact/sq_dev_ge0.
Qed.

Lemma sq_dev_max_ge0 : 0 <= sq_dev_max.
Proof. by rewrite /sq_dev_max; apply/topology.bigmax_geP; left. Qed.

Lemma sq_dev_max_ge u : C u != 0 -> sq_dev u <= sq_dev_max.
Proof. by move=> Cu0; rewrite /sq_dev_max; apply/le_bigmax_cond. Qed.

End sq_dev.

Section evar.
Local Open Scope ring_scope.

Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U)
  (PC0 : Weighted.total P C != 0).

Let WP := Weighted.d PC0.
Let X' := X : {RV WP -> R}.

Lemma evarE : `V_[X' | setT] = `V X'.
Proof. by rewrite Var_cVarT. Qed.

Lemma evar0P :
  reflect (forall i, C i * P i * sq_dev X PC0 i = 0) (`V X' == 0).
Proof.
rewrite /Var emean_sum.
apply: (iffP idP); last first.
  move=> H; under eq_bigr do rewrite H.
  by rewrite big1 // mul0r.
rewrite mulf_eq0 => /orP []; last first.
  by rewrite invr_eq0; have:= PC0; rewrite /Weighted.total=> /negPf ->.
move/[swap] => i.
rewrite psumr_eq0.
  by move/allP/(_ i)/[!mem_index_enum]/(_ erefl)/implyP/[!inE]/(_ erefl)/eqP->.
move=> x _; apply/mulr_ge0; last by rewrite sq_RV_pow2; exact/RleP/pow2_ge_0.
by apply/mulr_ge0=> //; exact/nneg_finfun_ge0.
Qed.

End evar.

Section pos_evar.
Local Open Scope ring_scope.

Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U).
Hypothesis (PC0 : Weighted.total P C != 0).
Let WP := Weighted.d PC0.
Let X' := X : {RV WP -> R}.
Hypothesis (evar_gt0 : 0 < `V X').

Lemma pos_evar_index :
  exists i, 0 < C i * P i * sq_dev X PC0 i.
Proof.
move: evar_gt0; rewrite lt_neqAle eq_sym => /andP [] /[swap] _.
case/evar0P/boolp.existsNP=> x /eqP ?; exists x.
rewrite lt_neqAle eq_sym; apply/andP; split=> //.
apply: mulr_ge0; last exact/sq_dev_ge0.
apply: mulr_ge0=> //; exact/nneg_finfun_ge0.
Qed.

End pos_evar.

Section invariant.
Local Open Scope ring_scope.

(**md ## eqn I, page 5 *)
Definition invariant (U : finType) (P : {fdist U}) (C : nneg_finfun U)
    (S : {set U}) (eps : R) :=
  \sum_(i in S) (1 - C i) * P i <=
  (1 - eps) / 2 * \sum_(i in ~: S) (1 - C i) * P i.

(**md ## page 62, line -1 *)
Definition invariantW (U : finType) (P : {fdist U}) (C : nneg_finfun U)
    (S : {set U}) (eps : R) (PC0 : Weighted.total P C != 0) :=
  let WP := Weighted.d PC0 in
  1 - eps <= Pr WP S.

End invariant.

Section bounding_empirical_mean.
Local Open Scope ring_scope.

Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U)
  (S : {set U}) (eps : R).

Let cplt_S := ~: S.

(* can be 1 /17 but not 1/ 15, failing at the end of bound_empirical_variance_S  *)
Local Notation eps_max := (1 / 16).
Hypotheses (C01 : is01 C) (PC0 : Weighted.total P C != 0)
  (pr_cplt_S : Pr P cplt_S = eps) (low_eps : eps <= eps_max).

Lemma pr_S : Pr P S = 1 - eps. Proof. by rewrite Pr_to_cplt pr_cplt_S. Qed.

Let eps0 : 0 <= eps. Proof. by rewrite -pr_cplt_S; exact/RleP/Pr_ge0. Qed.

Let WP := Weighted.d PC0.
Let X' := X : {RV WP -> R}.

Let tau := sq_dev X PC0.
Let tau_max := sq_dev_max X PC0.

Lemma pr_S_gt0 : 0 < Pr P S.
Proof. by rewrite pr_S; move: eps0 low_eps; lra. Qed.
Let hprSgt0 := pr_S_gt0.

Lemma weighted_total_gt0 : 0 < Weighted.total P C.
Proof. exact: Weighted.total_gt0. Qed.
Let hweightedtotalgt0 := weighted_total_gt0.

(**md ## eqn 1.1, page 5 *)
Lemma weight_contrib :
  (\sum_(i in S) C i * P i * tau i) / Pr P S <= `V_[X | S] + (`E_[X | S] - `E X')^+2.
Proof.
apply (@le_trans _ _ (`E_[tau | S])); last first.
  rewrite le_eqVlt/tau/sq_dev; apply/orP; left; exact/eqP/cVarDist/RltP.
rewrite cExE !coqRE ler_pM2r ?invr_gt0 //.
apply: ler_suml=> i HiS //.
  rewrite !coqRE (mulrC (tau i)) ler_wpM2r ?sq_dev_ge0 //.
  have /andP [_ c1] := C01 i.
  have hp := FDist.ge0 P i.
  by rewrite -{2}(mul1r (P i)); apply ler_wpM2r.
by rewrite mulr_ge0 // sq_dev_ge0.
Qed.

Let invariant := invariant P C S eps.
Let invariantW := invariantW S eps PC0.

Lemma invariant_impl : invariant -> invariantW.
Proof.
rewrite /invariant /invariantW /weightedmean.invariantW => hinv.
rewrite -!pr_S.
apply (@le_trans _ _ ((Pr P S / 2 *
                         (1 + Pr P S + (\sum_(i in cplt_S) C i * P i))) /
                        (\sum_i C i * P i))).
  rewrite -(@ler_pM2r _ ((\sum_i C i * P i) * 2)); last exact: mulr_gt0.
  rewrite !mulrA !(mulrC _ 2) -(mulrA _ _^-1) mulVf //.
  rewrite mulr1 !mulrA (mulrC _ (2^-1)) mulrA mulVf //; last by apply/eqP; lra.
  rewrite -addrA mulrDr mulr2n 2!mulrDl mul1r.
  apply:lerD; first by rewrite ler_pM2l // Weighted.total_le1'.
  rewrite ler_pM2l // addrC -bigID2.
  apply: ler_sum=> i HiU.
  case: ifPn => iS; first by [].
  rewrite -[leRHS]mul1r ler_wpM2r //.
  by have/andP[] := C01 i.
under [X in _ <= X]eq_bigr do rewrite Weighted.dE /Weighted.total.
rewrite -big_distrl /= ler_pM2r; last by rewrite invr_gt0.
rewrite -lerN2.
rewrite {2}pr_S addrA -addrA -pr_cplt_S mulrDr opprD addrC.
rewrite -lerBlDr.
rewrite opprK -mulrN addrC -mulrA mulVf; last by apply/eqP; lra.
rewrite mulr1 opprD opprK.
rewrite sumRE -!sumrN -!big_split /=.
have H E : \sum_(i in E) (P i + - (C i * P i)) = \sum_(i in E) (1 - C i) * P i.
  by apply eq_bigr => i _; rewrite mulrBl mul1r.
by rewrite !H pr_S.
Qed.

Lemma invariantW_pr_S_neq0 : invariantW -> Pr WP S != 0.
Proof.
rewrite /invariantW /invariantW /Pr -/WP=> H.
apply/lt0r_neq0/(lt_le_trans _ H).
by move: low_eps; lra.
Qed.

(**md ## eqn page 63, line 3 *)
Lemma bound_emean : invariantW ->
  (`E X' - `E_[X' | S])^+2 <= `V X' * 2 * eps / (1 - eps).
Proof.
move=> invC; have pSC:= invariantW_pr_S_neq0 invC.
have vhe0: 0 <= `V X' * 2 * eps / (1 - eps).
  rewrite mulr_ge0 // ?invr_ge0 // ?subr_ge0 // -?mulrA ?mulr_ge0 // ?variance_ge0' //.
  by move: low_eps; lra.
suff h : `| `E X' - `E_[X' | S] | <= Num.sqrt (`V X' * 2 * eps / (1 - eps)).
  rewrite -real_normK ?num_real // -[leRHS]sqr_sqrtr //.
  by rewrite lerXn2r // ?nnegrE ?sqrtr_ge0.
rewrite distrC {1}(_ : eps = 1 - (1 - eps)); last by lra.
set delta := 1 - eps.
apply: resilience'=> //.
by rewrite /delta; move: low_eps; lra.
Qed.

(**md ## eqn page 63, line 5 *)
Lemma S_mass : invariant ->
  1 - eps/2 <= (\sum_(i in S) C i * P i) / Pr P S.
Proof.
rewrite /is01 => Hinv.
have eps1_unit: 1 - eps != 0 by apply/eqP; move: low_eps eps0; lra.
apply (@le_trans _ _ (1 - (1 - eps) / 2 / Pr P S * Pr P cplt_S)).
  rewrite pr_cplt_S pr_S.
  by rewrite [in leRHS]mulrC mulrAC mulfV // div1r.
apply (@le_trans _ _ (1 - (1 - eps) / 2 / Pr P S *
                            \sum_(i in cplt_S) P i * (1 - C i))).
  rewrite lerD2l lerNl opprK ler_pM2l; last first.
    rewrite pr_S mulrC mulrA mulVf //; lra.
  apply ler_sum => i icplt_S.
  rewrite mulrBr mulr1 lerBlDr lerDl. apply: mulr_ge0 => //.
  by have /andP [] := C01 i.
rewrite -pr_S -mulrA mulrCA !mulrA mulVf ?pr_S // mul1r.
rewrite ler_pdivlMr; last by move: low_eps; lra.
rewrite -pr_S mulrDl mul1r {2}pr_S mulrC mulNr.
rewrite addrC; rewrite -lerBrDr lerNl opprD opprK addrC. (* mulrA.*)
rewrite -sumrN -big_split /=.
under eq_bigr do rewrite -{1}(mul1r (P _)) -mulNr -mulrDl.
under [in leRHS] eq_bigr do rewrite mulrC.
by rewrite mulrAC -mulrA mulrC; exact: Hinv.
Qed.

(**md ## eqn page 63, line 4 *)
Lemma bound_mean : invariant ->
  (`E_[X | S] - `E_[X' | S])^+2 <= `V X * 2 * eps / (2 - eps).
Proof.
move=> Hinv.
have -> : `E_[X | S] = `E_[Split.fst_RV C01 X | S `* [set: bool]].
  by rewrite -Split.cEx.
have -> : `E_[X' | S] = `E_[Split.fst_RV C01 X | S `* [set true]].
  by rewrite emean_cond_split.
rewrite sqrBC.
apply: (@le_trans _ _ (`V_[ Split.fst_RV C01 X | S `* [set: bool]] *
                         2 * (1 - (1 - eps / 2)) / (1 - eps / 2))).
  have V0: 0 <= `V_[ Split.fst_RV C01 X | S `* [set: bool]] *
                 2 * (1 - (1 - eps / 2)) / (1 - eps / 2).
    apply: mulr_ge0; last by rewrite invr_ge0; move: low_eps; lra.
    apply: mulr_ge0; last by move: eps0 low_eps; lra.
    apply: mulr_ge0 => //.
    exact: cvariance_ge0'.
  rewrite -ler_sqrt // sqrtr_sqr.
  apply: cresilience'.
    + move: low_eps; lra.
    + have := S_mass Hinv.
      rewrite -Split.Pr_setXT {2}/Pr big_setX/= -!coqRE => /le_trans; apply.
      rewrite sumRE le_eqVlt; apply/orP; left; apply/eqP.
      congr (_ / _)%coqR; apply: eq_bigr => u uS.
      by rewrite big_set1 Split.dE.
    + exact/setXS.
rewrite Split.cVar -(mulrA _ eps) -(mulrA _ (1 - _)).
rewrite !ler_pM// ?mulr_ge0 ?cvariance_ge0' ?invr_ge0//.
(* rewrite opprB addrCA subrr addr0. admit. *)
(* rewrite -mulrA -invfM mulrDr mulr1 mulrN. *)
(* rewrite mulrCA divff ?mulr1 //. *)
(* by apply/eqP; lra. *)
(* Qed. *)
Admitted.

(**md ## lemma 1.4, page 5 (part 1) *)
Lemma bound_mean_emean : invariant ->
  `| `E_[ X | S ] - `E X' | <= Num.sqrt (`V_[ X | S ] * 2 * eps / (2 - eps)) +
                           Num.sqrt (`V X' * 2 * eps / (1 - eps)).
Proof.
move=> IC.
have I1C : invariantW by exact: invariant_impl.
apply: (le_trans (ler_distD `E_[ X' | S ] `E_[ X | S ] (`E X'))).
have ? : 0 <= eps by rewrite -pr_cplt_S; apply/RleP/Pr_ge0.
apply: lerD.
- rewrite -(ger0_norm (sqrtr_ge0 _)).
  rewrite ler_abs_sqr sqr_sqrtr ?bound_mean //; admit.
  (* rewrite -!mulrA; apply/mulr_ge0; first exact: cvariance_ge0'. *)
  (* rewrite mulr_ge0 // mulr_ge0 // invr_ge0. *)
  (* by move: low_eps eps0; lra. *)
- rewrite distrC -(ger0_norm (sqrtr_ge0 _)).
  rewrite ler_abs_sqr sqr_sqrtr ?bound_mean //.
  + exact: bound_emean.
  + apply: mulr_ge0; last by rewrite invr_ge0; move: low_eps; lra.
    by rewrite mulr_ge0 // mulr_ge0 // variance_ge0'.
Admitted.

End bounding_empirical_mean.

(** WIP *)
Section update.
Local Open Scope ring_scope.

Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U).
Hypotheses (PC0 : Weighted.total P C != 0).

Let tau := sq_dev X PC0.
Let tau_max := sq_dev_max X PC0.

Definition arg_tau_max :=
  [arg max_(i > (fdist_supp_choice P) in [set: U]) tau i]%O.

Definition update_ffun : {ffun U -> R} :=
  [ffun i => if (tau_max == 0) || (C i == 0) then 0 else
            C i * (1 - tau i / tau_max)].

Lemma update_pos_ffun : [forall a, 0 <= update_ffun a]%mcR.
Proof.
apply/forallP=> i; apply/RleP.
rewrite /update_ffun ffunE.
case: ifPn; first by move=> ?; exact: Rle_refl.
case/norP=> tau_max_neq0 Ci_neq0.
apply/RleP/mulr_ge0; first exact/nneg_finfun_ge0.
rewrite subr_ge0 ler_pdivrMr ?mul1r; first exact/sq_dev_max_ge.
by rewrite lt_neqAle eq_sym tau_max_neq0/=; exact/sq_dev_max_ge0.
Qed.

Definition update : nneg_finfun U := mkNNFinfun update_pos_ffun.

End update.

(** part 2 of lemma 1.4 *)
Section bounding_empirical_variance.
Local Open Scope ring_scope.

Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U)
  (S : {set U}) (eps : R).

Let cplt_S := ~: S.

(* can be 1 /17 but not 1/ 15, failing at the end of bound_empirical_variance_S  *)
Local Notation eps_max := (1 / 16).

Hypotheses (C01 : is01 C) (PC0 : Weighted.total P C != 0)
  (pr_cplt_S : Pr P cplt_S = eps) (low_eps : eps <= eps_max).

Let WP := Weighted.d PC0.
Let X' := X : {RV WP -> R}.

Let eps0 : 0 <= eps. Proof. rewrite -pr_cplt_S. exact/RleP/Pr_ge0. Qed.

Let mu := `E_[X | S].
Let var := `V_[X | S].

Let mu_hat := `E X'.
Let var_hat := `V X'.

Let tau := sq_dev X PC0.
Let tau_max := sq_dev_max X PC0.

Let invariant := invariant P C S eps.
Let invariantW := invariantW S eps PC0.

(**md ## lemma 1.4, page 5 (part 2) *)
(**md ## eqn A.6--A.9, page 63 *)
Lemma bound_empirical_variance_S :
  16 * var <= var_hat ->
  invariant ->
  \sum_(i in S) C i * P i * tau i <= 1/4 * (1 - eps) * var_hat.
Proof.
move => var16 IC.
have I1C : invariantW. (* todo: repeated, factor out *)
  by apply: invariant_impl.
have Heps1 : 0 <= 1 - eps by move: low_eps; lra.
have Heps1' : 0 < 1 - eps by move: low_eps; lra.
have Heps2 : 0 <= 2 - eps by move: low_eps; lra.
have Heps2' : 0 < 2 - eps by move: low_eps; lra.
have Heps2'' : 0 <= 2 * eps by move: eps0; lra.
have H44eps2 : 0 <= 4 * 4 * (2 - eps) by move: low_eps; lra.
have Hvar_hat0 : 0 <= var_hat by exact: variance_ge0'.
have Hvar_hat_2_eps : 0 <= var_hat * 2 * eps
  by rewrite -mulrA; apply: mulr_ge0.
have Hvar0 : 0 <= var by exact: cvariance_ge0'.
rewrite /var_hat.
have ? := pr_S_gt0 pr_cplt_S low_eps.
(*a6*)
apply (@le_trans _ _ ((1 - eps) * (var + (mu - mu_hat)^+2))).
  by rewrite -!(pr_S pr_cplt_S) mulrC -ler_pdivrMr//; apply: weight_contrib => //; rewrite pr_cplt_S.
(*a6-a7*)
apply (@le_trans _ _ ((1 - eps) * (var + (Num.sqrt (var * 2 * eps / (2 - eps)) +
                                            Num.sqrt (var_hat * 2 * eps / (1 - eps)))^+2))).
  apply ler_wpM2l.
    by rewrite -pr_cplt_S subr_ge0; exact/RleP/Pr_1.
  rewrite lerD2l -ler_abs_sqr.
  rewrite [x in _ <= x]ger0_norm; first exact: bound_mean_emean.
  exact/addr_ge0/sqrtr_ge0/sqrtr_ge0.
(*a7-a8*)
apply (@le_trans _ _ ((1 - eps) * var_hat *
                        (16^-1 + 2 * eps *
                                 ((4 * Num.sqrt (2 - eps))^-1 + (Num.sqrt (1 - eps))^-1)^+2))).
  rewrite -(mulrA (1 - eps)).
  rewrite ler_wpM2l //.
  rewrite [leRHS]mulrDr lerD //; first lra.
  rewrite 2!mulrA -(sqr_sqrtr Hvar_hat_2_eps).
  rewrite -exprMn (mulrDr (Num.sqrt (var_hat * 2 * eps))).
  rewrite ler_sqr ?nnegrE; last 2 first.
  - by apply/addr_ge0/sqrtr_ge0/sqrtr_ge0.
  - by rewrite ?addr_ge0 ?mulr_ge0 ?invr_ge0 ?mulr_ge0 //;
         apply/RleP; rewrite -?RsqrtE';rewrite -!coqRE; try exact/sqrt_pos.
  apply: lerD.
    apply: (@le_trans _ _ (Num.sqrt (var_hat * 2 * eps * (4 * 4 * (2 - eps))^-1))); last first.
      rewrite sqrtrM // sqrtrV //.
      rewrite (sqrtrM (2 - eps)); last lra.
      by rewrite -expr2 sqrtr_sqr ger0_norm.
    rewrite ler_psqrt ?nnegrE; last 2 first.
    - apply: mulr_ge0; last by rewrite invr_ge0.
      by rewrite mulr_ge0 // mulr_ge0.
    - apply: mulr_ge0; last by rewrite invr_ge0.
      by rewrite mulr_ge0 // mulr_ge0.
    - rewrite invfM !mulrA ler_pM2r; last by rewrite invr_gt0.
      rewrite ler_pdivlMr; last lra.
      rewrite mulrC !mulrA (_ : 4 * 4 = 16); last lra.
      by rewrite -[leLHS]mulrA -[leRHS]mulrA ler_pM // mulr_ge0.
  by rewrite -sqrtrV // -sqrtrM // sqr_sqrtr.
(*a8-a9*)
apply (@le_trans _ _ ((1 - eps) * var_hat *
                        (1/16 + 2 * eps_max *
                                ((4 * Num.sqrt (2 - eps_max))^-1 +
                                   (Num.sqrt (1 - eps_max))^-1)^+2))).
  apply: ler_pM=> //.
  - exact:mulr_ge0.
  - apply:addr_ge0; first lra.
    rewrite mulr_ge0 //.
    exact: sqr_ge0.
  - apply: lerD; first by rewrite div1r.
    apply: ler_pM=> //; [exact: sqr_ge0|by move: low_eps; lra|].
    rewrite lerXn2r // ?nnegrE ?addr_ge0 //?invr_ge0 ?mulr_ge0 // ?sqrtr_ge0 //.
    by rewrite lerD ?lerXn2r // ?nnegrE ?addr_ge0 //?invr_ge0 ?mulr_ge0 // ?sqrtr_ge0 //;
      by rewrite ?lef_pV2 ?posrE ?mulr_gt0 // ?sqrtr_gt0 //; last lra;
      rewrite ?ler_pM2l // ler_wsqrtr // lerD2l lerN2.
rewrite /eps_max /= !coqRE.
rewrite mulrC mulrA ler_wpM2r // ler_wpM2r //.
by apply/RleP; rewrite -!coqRE -!RsqrtE'; interval.
Qed.

(**md ## eqn A.10--A.11, page 63 *)
Lemma bound_empirical_variance_cplt_S :
  16 * var <= var_hat ->
  invariant ->
  2/3 * var_hat <= \sum_(i in cplt_S) C i * P i * tau i.
Proof.
move => var16 HiC.
have ? := pr_S_gt0 pr_cplt_S low_eps.

have -> : \sum_(i in cplt_S) C i * P i * tau i =
  var_hat * (\sum_(i in U) C i * P i) - (\sum_(i in S) C i * P i * tau i).
  rewrite /var_hat evarE /Var {1}/Ex.
  apply/esym/eqP; rewrite subr_eq -bigID2 /=; under [eqRHS]eq_bigr do rewrite if_same.
  rewrite big_distrl /=; apply/eqP/eq_bigr=> i _.
  rewrite !coqRE /tau sq_devE [in RHS]mulrC !mulrA.
  rewrite Weighted.dE -/(Weighted.total P C).
  by rewrite -!mulrA !mul1r mulVf // mulr1.
apply:(@le_trans _ _ (var_hat * (1 - 3 / 2 * eps) -
                        \sum_(i in S) C i * P i * tau i)); last first.
  rewrite lerD2r ler_wpM2l // ?evar_ge0 //.
  apply: (@le_trans _ _ ((1 - eps / 2) * (1 - eps))); first nra.
  (*rewrite -(pr_S pr_cplt_S) /Pr.*)
  apply: (@le_trans _ _ (\sum_(i in S) C i * P i)).
    rewrite -(pr_S pr_cplt_S) -ler_pdivlMr; last by move: low_eps; lra.
    exact: S_mass.
  apply: ler_suml=> // i _ _.
  by rewrite mulr_ge0 // nneg_finfun_ge0.
apply (@le_trans _ _ ((1 - 3 / 2 * eps - 1/4 * (1 - eps)) * var_hat)); last first.
  by rewrite mulrBl (mulrC var_hat) lerD // lerN2 bound_empirical_variance_S.
rewrite ler_wpM2r // ?evar_ge0 //.
move: low_eps eps0; lra.
Qed.

(**md ## eqn 1.3--1.4, page 7 *)
(* TODO: improve the notation for pos_ffun (and for pos_fun) *)
Lemma update_removed_weight (E : {set U}) :
  let C' := update X PC0 in
  0 < tau_max ->
  \sum_(i in E) (1 - C' i) * P i =
    (\sum_(i in E) (1 - C i) * P i) +
    1 / tau_max * (\sum_(i in E) C i * P i * tau i).
Proof.
move => C' tau_max_gt0.
have <- : \sum_(i in E) (C i - C' i) * P i=
         1 / tau_max * (\sum_(i in E) C i * P i * tau i).
  rewrite /C' /update big_distrr.
  apply eq_bigr => i _ /=.
  rewrite /update_ffun-/tau_max-/tau ffunE.
  by case: ifPn => [/orP[/eqP|/eqP->]|]; lra.
by rewrite -big_split/=; apply eq_bigr => i HiE; rewrite -mulrDl addrA subrK.
Qed.

End bounding_empirical_variance.

Section update_invariant.
Local Open Scope ring_scope.

Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (C : nneg_finfun U)
  (S : {set U}) (eps : R).
Hypotheses (PC0 : Weighted.total P C != 0) (C01 : is01 C).
Let var_hat := evar X PC0.
Let var := `V_[X | S].
Let tau := sq_dev X PC0.
Let tau_max := sq_dev_max X PC0.

Hypotheses (pr_cplt_S : Pr P (~: S) = eps) (low_eps : eps <= 1/16)
  (var16 : 16 * var < var_hat).

Lemma sq_dev_max_neq0 : 0 < var_hat -> sq_dev_max X PC0 != 0.
Proof.
rewrite /sq_dev_max => var_hat_gt0.
have PCge0 := ltW (weighted_total_gt0 PC0).
move: var_hat_gt0.
rewrite /var_hat evarE /Var.
move=> /fsumr_gt0[i _] /RltP; rewrite !coqRE.
rewrite Weighted.dE => /[dup] => /wpmulr_lgt0 => sq_dev_gt0.
have:= sq_RV_ge0 (X `-cst \sum_(v in U) X v * Weighted.d PC0 v) i=> /RleP/wpmulr_rgt0/[apply].
have:= PCge0; rewrite -invr_ge0=> /wpmulr_lgt0 /[apply].
have /[apply] Cigt0 := wpmulr_lgt0 (FDist.ge0 P i).
rewrite gt_eqF //; apply/bigmax_gt0_seq; exists i.
split=> //; first by rewrite gt_eqF.
by rewrite sq_devE sq_dev_gt0 // mulr_ge0 // ?mulr_ge0 // ?nneg_finfun_ge0 // invr_ge0 PCge0.
Qed.

(**md ## lemma 1.5, page 5, update preserves the invariant of filter1D *)
Lemma invariant_update : let C' := update X PC0 in
  invariant P C S eps -> invariant P C' S eps.
Proof.
rewrite /invariant => inv.
have var_ge0 : 0 <= var by exact: cvariance_ge0'.
have tau_max_gt0 : 0 < sq_dev_max X PC0.
  by rewrite lt_neqAle eq_sym sq_dev_max_neq0 ?sq_dev_max_ge0 //; move: var16; lra.
suff H2 : \sum_(i in S) (C i * P i) * tau i <=
    (1 - eps) / 2 * (\sum_(i in ~: S) (C i * P i) * tau i).
  rewrite !update_removed_weight// !mulrDr; apply lerD; first exact inv.
  rewrite mulrCA; rewrite ler_pM2l; [exact: H2 | exact: divr_gt0].
have var16':= ltW var16.
apply: le_trans; first exact: (bound_empirical_variance_S C01 pr_cplt_S).
rewrite -ler_pdivrMl; last by apply: divr_gt0; move: low_eps; lra.
rewrite invf_div !mulrA.
have -> : 2 / (1 - eps) * 1/4 * (1 - eps) = 1/2 * ((1-eps) / (1-eps)) by lra.
rewrite divrr ?mulr1; last by rewrite unitfE; move: low_eps; lra.
apply: le_trans; last exact: (bound_empirical_variance_cplt_S C01 pr_cplt_S).
by rewrite ler_wpM2r //; [exact: evar_ge0|lra].
Qed.

Lemma is01_update : is01 (update X PC0).
Proof.
move=> u; apply/andP; split; first by have/forallP := update_pos_ffun X PC0.
rewrite /update_ffun ffunE; case: ifPn; first lra.
rewrite negb_or => /andP[sq_dev_neq0 Cu_neq0].
apply: mulr_ile1.
- exact: nneg_finfun_ge0.
- rewrite subr_ge0 ler_pdivrMr// ?mul1r//; last first.
    by rewrite lt_neqAle eq_sym sq_dev_neq0/=; exact: sq_dev_max_ge0.
  exact: sq_dev_max_ge.
- by have/andP[]:= C01 u.
- by rewrite lerBlDr addrC -lerBlDr subrr divr_ge0 // ?sq_dev_ge0 // sq_dev_max_ge0.
Qed.

End update_invariant.

Section base_case.
Local Open Scope ring_scope.

(* TODO: define a proper environment *)
Variables (A : finType) (P : {fdist A}) (eps : R) (S : {set A}).

Definition ffun1 : {ffun A -> R} := [ffun=> 1].
Let ffun1_subproof : [forall a, 0 <= ffun1 a].
Proof. by apply/forallP => u; rewrite ffunE; apply/RleP. Qed.
Definition Cpos_ffun1 := @mkNNFinfun A ffun1 ffun1_subproof.

Lemma PC1_neq0 : Weighted.total P Cpos_ffun1 != 0.
Proof.
rewrite/Weighted.total.
under eq_bigr => i _ do rewrite /Cpos_ffun1/=/ffun1 ffunE mul1r.
rewrite FDist.f1.
apply oner_neq0.
Qed.

Lemma C1_is01 : is01 Cpos_ffun1.
Proof. by move => i; rewrite ffunE; lra. Qed.

Lemma base_case: Pr P (~: S) = eps ->
  invariant P Cpos_ffun1 S eps.
Proof.
move=> Hcplt_S_ratio; rewrite /invariant.
rewrite /Cpos_fun /=.
under eq_bigr do rewrite ffunE subrr mul0r.
rewrite big1; last by [].
under eq_bigr do rewrite ffunE subrr mul0r.
rewrite big1; last by [].
by rewrite mulr0.
Qed.

End base_case.

Require Import FunInd Recdef.

Notation "a '<=?' b" := (Bool.bool_dec (Rleb a b) true).
Notation "a '!=?' b" := (Bool.bool_dec (a != b) true) (at level 70).

(**md ## Algorithm 2, page 4 *)
Section filter1D.
Local Open Scope ring_scope.

Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}).

Local Obligation Tactic := idtac.

Lemma filter1D_arg_decreasing (C : nneg_finfun U) (var : R) :
  0 <= var -> is01 C ->
  forall PC0 : Weighted.total P C != 0,
  forall K : Rleb (evar X PC0) (16 * var) <> true,
  (#|0.-support (update X PC0)| < #|0.-support C|)%coq_nat.
Proof.
rewrite/Weighted.total=> var_ge0 C01 PCneq0 /negP/RlebP/RleP.
rewrite -ltNge !coqRE=> evar16.
apply/ssrnat.ltP/proper_card/properP; split.
  apply/subsetP => u; rewrite !supportE /update_ffun ffunE.
  by case: ifPn; [rewrite eqxx|rewrite negb_or => /andP[]].
have PCgt0 := weighted_total_gt0 PCneq0.
have PCge0 := ltW PCgt0.
move: (PCgt0) => /fsumr_gt0[u _ /RltP].
rewrite mulr_ge0_gt0// => [/andP[Cu0 Pu0]|]; last by have/andP[]:= C01 u.
have Cmax_neq0 : C [arg max_(i > u | C i != 0) sq_dev X PCneq0 i]%O != 0.
  by case: arg_maxP => //; rewrite gt_eqF.
have sq_dev_max_neq0 : sq_dev_max X PCneq0 != 0.
  apply/sq_dev_max_neq0/(le_lt_trans _ evar16).
  by rewrite mulr_ge0 //; apply/ltW/RltP/IPR_gt_0.
exists [arg max_(i > u | C i != 0) sq_dev X PCneq0 i]%O.
  by rewrite supportE.
rewrite /update_ffun supportE ffunE negbK ifF.
  rewrite mulf_eq0 subr_eq0 -invr1 -(mul1r (1^-1))%mcR.
  rewrite eqr_div ?oner_eq0// ?mulr1 ?mul1r// /sq_dev_max.
  rewrite (@bigmax_eq_arg _ _ _ _ u) ?eq_refl ?orbT ?gt_eqF//.
  by move=> i _; exact/sq_dev_ge0.
by rewrite (negbTE sq_dev_max_neq0)/=; exact/negbTE.
Qed.

Function filter1D_rec var (var_ge0 : 0 <= var)
    (C : nneg_finfun U) (C01 : is01 C) (PC0 : Weighted.total P C != 0)
    {measure (fun C => #| 0.-support C |) C} :=
  if evar X PC0 (* empirical var. *) <=? 16 * var is left _ then
    Some (emean X PC0) (* empirical mean *)
  else
    let C' := update X PC0 in
    if Weighted.total P C' !=? 0 is left PC0' then
      filter1D_rec var_ge0 (is01_update X PC0 C01) PC0'
    else
      None.
Proof.
rewrite/Weighted.total=> var var_ge0 C C01 PC0 evar16 h2 h3 _.
exact: (filter1D_arg_decreasing var_ge0).
Qed.

Definition filter1D var (var_ge0 : 0 <= var) := filter1D_rec var_ge0 (@C1_is01 U) (PC1_neq0 P).

End filter1D.



Section filter1D_correct.
Local Open Scope ring_scope.

Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}) (S : {set U}) (eps : R).
Hypotheses (pr_cplt_S : Pr P (~: S) = eps) (low_eps : eps <= 1/16).
Let mu := `E_[X | S].
Let var := `V_[X | S].
Let var_ge0 := cvariance_ge0' X S.
Let eps0 : 0 <= eps. Proof. rewrite -pr_cplt_S. exact/RleP/Pr_ge0. Qed.

Functional Scheme filter1D_rec_ind := Induction for filter1D_rec Sort Prop.

Lemma filter1D_correct :
  if filter1D X var_ge0 is Some mu_hat
  then `| mu - mu_hat | <= Num.sqrt (var * (2 * eps) / (2 - eps)) +
                          Num.sqrt (16 * var * (2 * eps) / (1 - eps))
  else false.
Proof.
have sixteenE: 16%coqR = 16 by rewrite /16%coqR -INR_IPR /= coqRE.
rewrite /filter1D.
have tr x y : Rleb x y <> true -> y < x by move=> /negP/RlebP/RleP; rewrite -ltNge.
have tr' x y : Rleb x y = true -> x <= y by move=> /RlebP/RleP.
have pr_S := pr_S pr_cplt_S.
have := base_case pr_cplt_S.
apply filter1D_rec_ind => //=.
- move=> C C01 PC0 /tr' evar16 _ Inv.
  apply: le_trans; first by apply bound_mean_emean => //; rewrite pr_cplt_S//.
  apply lerD; first by rewrite pr_cplt_S mulrA.
  rewrite ler_wsqrtr // -pr_S -Pr_to_cplt' ler_wpM2r //.
    by rewrite invr_ge0 pr_S; move: low_eps; lra.
  rewrite pr_cplt_S -mulrA ler_wpM2r //; first by move: eps0; lra.
  by move: evar16; rewrite !coqRE (_ : 16%coqR = 16).
- move=> C C01 PC_neq0 [//|/=] evar16 _ _ PC0 _ IH Inv.
  apply/IH/invariant_update => //.
  by move/tr: evar16; rewrite !coqRE sixteenE.
- move=> C C01 PC0 [//|] evar16 _ /= _ [//|/=] PC_eq0 _ /= _.
  move/tr: evar16; rewrite !coqRE sixteenE.
  move=> evar16 /(invariant_update C01 pr_cplt_S low_eps evar16).
  have PC0' : forall x, update X PC0 x * P x = 0.
    move: PC_eq0=> /negP/negbNE; rewrite psumr_eq0;
      last by move=> i _; rewrite mulr_ge0 ?nneg_finfun_ge0.
    by move/allP=> PC0' x; apply/eqP/PC0'/mem_index_enum.
  rewrite /invariant.
  under eq_bigr do rewrite mulrDl mulNr PC0' subr0 mul1r.
  under [in leRHS]eq_bigr do rewrite mulrDl mulNr PC0' subr0 mul1r.
  rewrite -/(Pr P (~: S)) pr_cplt_S -/(Pr P S) pr_S.
  have->: false <-> False :> Prop by [].
  apply/negP; rewrite -ltNge.
  by rewrite -mulrA gtr_pMr; move: low_eps; lra.
Qed.

Corollary filter1D_converges : filter1D X var_ge0 != None.
Proof. by move: filter1D_correct; case: (filter1D X var_ge0). Qed.

End filter1D_correct.
