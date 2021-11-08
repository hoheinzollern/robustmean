From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg matrix.
From mathcomp Require Import all_algebra. (* for GRing.Theory *)
From mathcomp Require boolp classical_sets. (* classical_sets for pointedType *)
From mathcomp Require Import Rstruct topology. (* topology for fct_ringType *)
Require Import Reals Lra ROrderedType.
From infotheo Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext.
From infotheo Require Import Rbigop proba fdist.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope proba_scope.
Local Open Scope R_scope.

(*
Definition mul_RV (U : finType) (P : fdist U) (X Y : {RV (P) -> (R)}) (x : U) :=
  X x * Y x.
Notation "X `* Y" := (mul_RV X Y) : proba_scope.
*)
Notation "X `* Y" := (fun x => X x * Y x) : proba_scope.

Section sets_functions.

Lemma set1I (X:finType) (x:X) (A:{set X}) :
  [set x] :&: A = if x \in A then [set x] else set0.
Proof.
  case: ifPn => H0.
  - by apply/setIidPl; rewrite sub1set.
  - by apply/disjoint_setI0; rewrite disjoints1 H0.
Qed.

Lemma in_preim1 (A:finType) (B:eqType) (a:A) (b:B) X :
  (a \in finset (T:=A) (preim X (pred1 b))) -> X a = b.
Proof. by rewrite in_set => /eqP. Qed.

Lemma in_preim1' (A:finType) (B:eqType) (a:A) (b:B) X :
  (a \in finset (T:=A) (preim X (pred1 b))) = (X a == b).
Proof.
  apply/idP; case H: (X a == b); first by move/eqP: H <-; rewrite inE /= eqxx.
  by move: H=> /[swap] /in_preim1 ->; rewrite eqxx.
Qed.

Lemma leq_sumR I r (P : pred I) (E1 E2 : I -> R) :
    (forall i, P i -> E1 i <= E2 i) ->
  \sum_(i <- r | P i) E1 i <= \sum_(i <- r | P i) E2 i.
Proof. move=> leE12. elim/big_ind2: _ => // m1 m2 n1 n2. lra. Qed.

Lemma Ind_subset (A : finType) (X Y : {set A}) :
  X \subset Y <-> forall a, Ind X a <= Ind Y a.
Proof.
rewrite /Ind; split => H.
  by move=> a; case: ifPn; [move/(subsetP H) -> | case: (a \in Y)].
apply/subsetP => a aX.
move: (H a); rewrite aX; case: (a \in Y) => //.
by move/leRNgt/(_ Rlt_0_1).
Qed.

End sets_functions.

(* NB: will appear in the next version of infotheo *)
Lemma eqR_divl_mulr (z x y : R) : z != 0 -> (x = y / z) <-> (x * z = y).
Proof. by move=> z0; split; move/esym/eqR_divr_mulr => /(_ z0) ->. Qed.

Delimit Scope ring_scope with ring.

Section RV_ring.
Variables (U : finType) (P : fdist U).
Import topology.
Import GRing.Theory.

Lemma add_RV_addr (X Y : {RV P -> R}) : X `+ Y = (X + Y)%ring.
Proof. reflexivity. Qed.

Lemma sub_RV_subr (X Y : {RV P -> R}) : X `- Y = (X - Y)%ring.
Proof. reflexivity. Qed.

Lemma trans_min_RV_subr (X : {RV P -> R}) (y : R) :
  X `-cst y = (X - cst y)%ring.
Proof. reflexivity. Qed.

Definition fdist_supp_choice : U.
by move/set0Pn/xchoose:(fdist_supp_neq0 P).
Defined.

Canonical fdist_supp_pointedType :=
  @classical_sets.Pointed.pack U fdist_supp_choice _ _ idfun.

Lemma mul_RV_mulr (X Y : {RV P -> R}) : X `* Y = (X * Y)%ring.
Proof. reflexivity. Qed.

Lemma sq_RV_sqrr (X : {RV P -> R}) : X `^2 = (X ^+ 2)%ring.
Proof. by rewrite /sq_RV/comp_RV; apply boolp.funext => u /=; rewrite mulR1. Qed.

Definition RV_ringE :=
  (add_RV_addr, sub_RV_subr, trans_min_RV_subr, mul_RV_mulr, sq_RV_sqrr).
End RV_ring.


Section probability.
Variables (U : finType) (P : fdist U).
Import GRing.Theory.

Lemma Pr_lt1 (E : {set U}) : Pr P E < 1 <-> Pr P E != 1.
Proof.
rewrite Pr_to_cplt.
rewrite -[X in _ < X]addR0.
rewrite ltR_add2l.
rewrite -subR_eq0' -!addR_opp addRAC addRN add0R.
move:oppR_lt0; rewrite /Rgt=> H; rewrite -H.
rewrite oppR_eq0.
exact: Pr_gt0.
Qed.

Lemma sq_RVE (X : {RV P -> R}) : X `^2 = X `* X.
Proof. by rewrite sq_RV_sqrr. Qed.

Lemma Ind_ge0 (X : {set U}) (x : U) : 0 <= Ind X x.
Proof. by rewrite /Ind; case: ifPn. Qed.

Lemma Ind_setD (X Y : {set U}) :
  Y \subset X -> Ind (X :\: Y) = Ind X `- Ind Y :> {RV P -> R}.
Proof.
move/subsetP=> YsubX; rewrite /Ind /sub_RV. apply boolp.funext => u /=.
case: ifPn; rewrite inE ?negb_and;
  first by case/andP => /negbTE -> ->; rewrite subR0.
case/orP; first by move => /negbNE /[dup] /YsubX -> ->; rewrite subRR.
move/contraNN: (YsubX u) => YsubX'.
move=> /[dup] /YsubX' /negbTE -> /negbTE ->.
by rewrite subRR.
Qed.

Lemma cEx_ExInd (X : {RV P -> R}) F :
  `E_[X | F] = `E (X `* Ind (A:=U) F : {RV P -> R}) / Pr P F.
Proof.
rewrite /Pr /cEx (* need some lemmas to avoid unfolds *) -big_distrl /=.
congr (_ / _).
under eq_bigr => i _.
  rewrite big_distrr.
  have -> :
    \sum_(i0 in finset (preim X (pred1 i)) :&: F) (i * P i0) =
    \sum_(i0 in finset (preim X (pred1 i)) :&: F)
     (X i0 * @Ind U F i0 * P i0).
    apply congr_big => // i0.
    rewrite in_setI /Ind => /andP[] /in_preim1 -> ->.
    by rewrite mulR1.
  have H1 :
    \sum_(i0 in finset (preim X (pred1 i)) :\: F) X i0 * Ind F i0 * P i0 = 0.
  (* This should be true because all elements of the sum are 0 *)
    rewrite big1 // => i1.
    rewrite in_setD => /andP [H2 H3].
    by rewrite /Ind (negbTE H2) mulR0 mul0R.
  have :
    \sum_(i0 in finset (preim X (pred1 i))) X i0 * Ind F i0 * P i0 =
    \sum_(i0 in finset (preim X (pred1 i)) :&: F) X i0 * Ind F i0 * P i0 +
    \sum_(i0 in finset (preim X (pred1 i)) :\: F) X i0 * Ind F i0 * P i0
    by apply big_setID.
  rewrite H1 addR0 => <-.
  under eq_bigl do rewrite in_preim1'.
  by over.
by rewrite -sum_parti_finType.
Qed.

Lemma sq_RV_ge0 (X : {RV P -> R}) x : 0 <= (X `^2) x.
Proof. exact: pow2_ge_0. Qed.

Lemma Ex_square_ge0 (X : {RV P -> R}) : 0 <= `E (X `^2).
Proof. exact/Ex_ge0/sq_RV_ge0. Qed.

Lemma Ex_square_expansion a b (X Y : {RV P -> R}):
  `E ((a `cst* X `+ b `cst* Y) `^2) =
  a * a * `E (X `^2) + b * b * `E (Y `^2) + 2 * a * b * `E (X `* Y:{RV P -> R}).
Proof.
suff : `E ((a `cst* X `+ b `cst* Y) `^2) =
       `E ((a * a) `cst* (X `^2) `+
       (b * b) `cst* (Y `^2) `+ (2 * a * b) `cst* (X `* Y)).
  by rewrite !E_add_RV !E_scalel_RV.
apply eq_bigr => i H.
unfold ambient_dist, "`cst*", "`+", "`^2", "`o", "^".
nra.
Qed.

Lemma Ex_square_eq0 X :
  (forall x, X x = 0 \/ P x = 0) <-> `E (X `^2 : {RV P -> R}) = 0.
Proof.
split=> [XP|EX20].
- rewrite /Ex big1// => u _.
  have [|->] := XP u; last by rewrite mulR0.
  by rewrite /sq_RV /comp_RV /= => ->; rewrite !mul0R.
- have XP : forall x, x \in U -> (X `^2: {RV P -> R}) x * P x = 0.
    apply: ((psumR_eq0P _).1 EX20).
    by move=> u _; apply/mulR_ge0; [exact: sq_RV_ge0|exact: FDist.ge0].
  move=> x.
  have := XP x.
  rewrite inE => /(_ erefl) /mulR_eq0[|->]; last by right.
  by rewrite /sq_RV /comp_RV /= mulR1 => /mulR_eq0[|] ->; left.
Qed.

Lemma Cauchy_Schwarz_proba (X Y : {RV P -> R}):
  Rsqr (`E (X `* Y : {RV P -> R})) <= `E (X `^2) * `E (Y `^2).
Proof.
pose a := sqrt (`E (Y `^2)).
pose b := sqrt (`E (X `^2)).
have H2ab : 2 * a * b * (b * a) = a * a * `E (X `^2) + b * b * `E (Y `^2).
  rewrite -(Rsqr_sqrt (`E (X `^2))); last exact: Ex_square_ge0.
  rewrite -(Rsqr_sqrt (`E (Y `^2))); last exact: Ex_square_ge0.
  by rewrite -/a -/b /Rsqr; nra.
have [a0|a0] := Req_dec a 0.
  apply sqrt_eq_0 in a0; last exact: Ex_square_ge0.
  have HY : forall y, Y y = 0 \/ P y = 0 by apply/Ex_square_eq0/a0.
  have -> : `E (X `* Y: {RV P -> R}) = 0.
    apply psumR_eq0P => u uU.
      by case : (HY u) => -> ; rewrite mulR0 ?mul0R; apply leRR.
    by case : (HY u) => -> ; rewrite mulR0 ?mul0R.
  by rewrite Rsqr_0; apply/mulR_ge0; apply Ex_square_ge0.
have [b0|b0] := Req_dec b 0.
  apply sqrt_eq_0 in b0; last exact: Ex_square_ge0.
  have HX : forall x, X x = 0 \/ P x = 0 by apply /Ex_square_eq0/b0.
  have -> : `E (X `* Y: {RV P -> R}) = 0.
    apply psumR_eq0P => u uU.
      by case : (HX u) => -> ; rewrite ?mulR0 ?mul0R; apply leRR.
    by case : (HX u) => -> ; rewrite ?mulR0 ?mul0R.
  by rewrite Rsqr_0; apply/mulR_ge0; apply Ex_square_ge0.
have {}a0 : 0 < a (*removes a0 hypothesis and reuse it*)
  by apply/ltR_neqAle; split; [exact/nesym|exact/sqrt_pos].
have {}b0 : 0 < b
  by apply/ltR_neqAle; split; [exact/nesym|exact/sqrt_pos].
rewrite -(Rsqr_sqrt (_ * _)); last by apply/mulR_ge0; apply Ex_square_ge0.
rewrite sqrt_mult; [|exact: Ex_square_ge0|exact: Ex_square_ge0].
rewrite -/a -/b.
apply: neg_pos_Rsqr_le.
- rewrite -(@leR_pmul2r (2 * a * b)); last first.
    by apply mulR_gt0 => //; apply mulR_gt0.
  rewrite -subR_ge0 mulNR subR_opp addRC mulRC H2ab.
  by rewrite (mulRC (`E (X `* Y))) -Ex_square_expansion; exact: Ex_square_ge0.
- apply/(@leR_pmul2l (2 * a * b)); first by do 2 apply: mulR_gt0 => //.
  apply/subR_ge0; rewrite H2ab -(Rmult_opp_opp b) -addR_opp -mulNR -mulRN.
  by rewrite -Ex_square_expansion; exact: Ex_square_ge0.
Qed.

Lemma I_square F : Ind F = ((Ind F) `^2 : {RV P -> R}).
Proof.
rewrite sq_RVE boolp.funeqE /Ind => x.
by case: ifPn; rewrite ?mulR0 ?mulR1.
Qed.

Lemma I_double F : Ind F = ((Ind F) `* (Ind F) : {RV P -> R}).
Proof. by rewrite [LHS]I_square sq_RVE. Qed.

(*
Lemma I_mult_one F : (Ind (A:=U) F : {RV P -> R}) `* 1 = Ind (A:=U) F.
(F: {RV P -> R}): (Ind (A:=U) F: {RV P -> R}) `* 1 = (Ind (A:=U) F : {RV P -> R}). *)

Lemma cEx_sub (X : {RV P -> R}) (F G: {set U}) :
  0 < Pr P F ->
  F \subset G ->
  `| `E_[ X | F ] - `E_[X | G] |
= `| `E ((X `-cst `E_[X | G]) `* Ind F : {RV P -> R}) | / Pr P F.
Proof.
move=> /[dup] /Pr_gt0 PrPF_neq0 /invR_gt0 /ltRW PrPFV_ge0 FsubG.
rewrite divRE -(geR0_norm (/Pr P F)) // -normRM.
congr `| _ |.
rewrite !RV_ringE mulrDl mulNr.
by rewrite E_sub_RV mulRDl E_scalel_RV E_Ind mulNR -mulRA mulRV // mulR1 cEx_ExInd.
Qed.

Lemma Ex_cExT (X : {RV P -> R}) : `E X = `E_[X | [set: U]].
Proof.
rewrite /cEx.
under eq_bigr do rewrite setIT Pr_setT divR1 -pr_eqE.
(* The names of lemmas for Pr are inconsistent:
   some begin with "Pr" while others "pr" *)
by rewrite -Ex_comp_RV; congr `E.
Qed.

Definition cVar (X : {RV P -> R}) F
  := let miu := `E_[X | F] in `E_[(X `-cst miu) `^2 | F].
Notation "`V_[ X | F ]" := (cVar X F).

Lemma Var_cVarT (X : {RV P -> R}) : `V X = `V_[X | [set: U]].
Proof. by rewrite /cVar -!Ex_cExT. Qed.

Lemma cEx_cVar (X : {RV P -> R}) (F G: {set U}) : 0 < Pr P F  ->
  F \subset G ->
  let mu := `E_[X | G] in
  let var := `V_[X | G] in
  `| `E_[ X | F ] - mu | <= sqrt (var * Pr P G / Pr P F ).
Proof.
move=> /[dup] /invR_gt0 /ltRW PrPFV_nneg /[dup] /invR_gt0
        PrPFV_pos /[dup] /Pr_gt0 PrPF_neq0 PrPF_pos
        /[dup] /(Pr_incl P) /(ltR_leR_trans PrPF_pos)
        /[dup] /Pr_gt0 PrPG_neq0 PrPG_pos FsubG mu var.
rewrite cEx_sub //.
pose y := sqrt (Ex P (((X `-cst mu) `^2) `* Ind F) * Ex P (Ind F)) / Pr P F.
apply leR_trans with (y := y).
  rewrite divRE leR_pmul2r // -sqrt_Rsqr_abs.
  apply sqrt_le_1_alt.
  have -> : (X `-cst mu) `* Ind F = (X `-cst mu) `* Ind F `* Ind F
    by rewrite {1}I_double boolp.funeqE=> u; rewrite mulRA.
  apply/(leR_trans (Cauchy_Schwarz_proba _ _))/leR_eqVlt; left.
  congr (_ * _); congr (`E _); last by rewrite -I_square.
  by rewrite [in RHS]I_double !RV_ringE !expr2 mulrCA !mulrA.
rewrite /y divRE -(sqrt_Rsqr (/ Pr P F)) // -sqrt_mult_alt; last first.
  move=> *; apply mulR_ge0; last by rewrite E_Ind.
  by apply: Ex_ge0 => u; apply: mulR_ge0; [apply pow2_ge_0 | apply Ind_ge0].
apply sqrt_le_1_alt.
rewrite /var /cVar -/mu cEx_ExInd !E_Ind /Rsqr.
rewrite mulRCA -!mulRA mulRV // mulR1 mulRC.
rewrite [X in _ * X / _]mulRC mulRV // mulR1 divRE.
apply leR_wpmul2r => //.
apply leq_sumR=> i iU.
rewrite -mulRA -[X in _ <= X]mulRA; apply leR_wpmul2l; first exact: sq_RV_ge0.
by apply leR_pmul => //; [exact: Ind_ge0 | move/Ind_subset: FsubG | exact: leRR].
Qed.

(*prove A1 and A3 for later use*)
Lemma cEx_Var (X : {RV P -> R}) F : 0 < Pr P F  ->
  `| `E_[ X | F ] - `E X | <= sqrt (`V X / Pr P F ).
Proof.
move=> H; rewrite Ex_cExT Var_cVarT.
move: (@cEx_cVar X F [set: U] H) => /=.
by rewrite Pr_setT mulR1 subsetT; apply.
Qed.

Lemma cEx_cptl (X: {RV P -> R}) F:
  0 < Pr P F -> Pr P F < 1 ->
    `E_[X | F] * Pr P F + `E_[X | (~: F)] * Pr P (~: F) = `E X.
Proof.
  move => PrFgt0 PrFlt1.
  repeat rewrite cEx_ExInd.
  unfold Rdiv.
  repeat rewrite big_distrl.
  rewrite -big_split.
  apply congr_big; auto.
  move => i HiU. simpl.
  unfold "`p_", Ind.
  repeat rewrite -mulRA.
  repeat rewrite mulVR.
  repeat rewrite mulR1.
  rewrite in_setC.
  destruct (i \in F); simpl; lra.
  all: apply Pr_gt0; try rewrite Pr_of_cplt; lra.
Qed.

Lemma cEx_Inv_int (X: {RV P -> R}) F:
0 < Pr P F -> Pr P F < 1 ->
  Pr P F * (`E_[X | F] - `E X) = Pr P (~: F) * - (`E_[X | (~: F)] - `E X).
Proof.
  move => H H0.
  rewrite mulRDr oppRD mulRDr oppRK mulRN mulRN.
  repeat rewrite cEx_ExInd.
  (repeat have ->: forall x y, x != 0 -> x * (y / x) = y
  by move => x y Hz; rewrite mulRC -mulRA mulVR; last by []; rewrite mulR1);
  try apply Pr_gt0; try rewrite Pr_of_cplt; try lra.
  apply Rplus_eq_reg_r with (r:= Pr P F * `E X).
  rewrite -addRA Rplus_opp_l addR0 -addRA addRC.
  apply Rplus_eq_reg_r with (r:=`E (X `* Ind (~: F):{RV P -> R})).
  rewrite -addRA Rplus_opp_l addR0 -big_split.
  rewrite mulRDl -addRA mulNR Rplus_opp_l addR0 mul1R.
  apply congr_big; auto.
  move => i HiU. simpl.
  unfold "`p_".
  rewrite -mulRDl.
  congr (_ * _).
  unfold Ind.
  rewrite in_setC.
  elim (i \in F); simpl; lra.
Qed.

Lemma cEx_Inv' (X: {RV P -> R}) (F G : {set U}) :
  0 < Pr P F -> F \subset G -> Pr P F < Pr P G ->
  `| `E_[X | F] - `E_[X | G]| = (Pr P (G :\: F)) / (Pr P F) * `| `E_[X | (G :\: F)] - `E_[X | G]|.
Proof.
move=> PrPF_gt0 /[dup] /setIidPr GIFF FsubG /[dup] /(ltR_trans PrPF_gt0)
       /[dup] /Pr_gt0 /invR_neq0' /eqP PrPG_neq0 PrPG_gt0 PrPF_PrPG.
have : 0 < Pr P (G :\: F) by rewrite Pr_diff subR_gt0 GIFF.
move => /[dup] /Pr_gt0 PrPGF_neq0 PrPGF_gt0.
rewrite !cEx_sub ?subsetDl // !divRE mulRCA.
rewrite Ind_setD // !RV_ringE mulrDr mulrN E_sub_RV.
have -> : Ex P ((X `-cst `E_[X | G]) `* Ind G) = 0.
  apply normR0_eq0.
  by rewrite -(@eqR_mul2r (/ Pr P G)) // -divRE -cEx_sub // subRR normR0 mul0R.
rewrite sub0R normRN.
by rewrite [X in _ = _ * X]mulRAC mulRV // mul1R.
Qed.

(* NB: not used *)
Lemma cEx_Inv (X: {RV P -> R}) F :
  0 < Pr P F -> Pr P F < 1 ->
  `| `E_[X | F] - `E X| = (1 - Pr P F) / Pr P F * `| `E_[X | (~: F)] - `E X|.
Proof.
move=> *; rewrite Ex_cExT -Pr_of_cplt -setTD; apply cEx_Inv' => //.
apply ltR_neqAle; split; last by apply/Pr_incl/subsetT.
by apply/eqP; rewrite Pr_setT -Pr_lt1.
Qed.

(* /[conj] by Cyril Cohen :
   https://coq.zulipchat.com/#narrow/stream/237664-math-comp-users/topic/how.20to.20combine.20two.20top.20assumptions.20with.20.60conj.60
 *)
Lemma and_curry (A B C : Prop) : (A /\ B -> C) -> A -> B -> C.
Proof. move=> + a b; exact. Qed.

Notation "[conj]" := (ltac:(apply and_curry)) (only parsing) : ssripat_scope.

Lemma cvariance_nonneg (X : {RV P -> R}) F : 0 <= `V_[X | F].
Proof.
have [/ltRP H|] := boolP (0 <b Pr P F); last first.
  rewrite -leRNlt' => /leRP.
  move: (Pr_ge0 P F) => /[conj] /eqR_le H.
  rewrite /cVar /cEx; apply big_ind; [exact: leRR|exact: addR_ge0|move=> i _].
  by rewrite setIC Pr_domin_setI // mulR0 divRE mul0R; apply leRR.
rewrite /cVar cEx_ExInd /Ex /ambient_dist divRE big_distrl /=.
apply sumR_ge0 => u _; apply mulR_ge0; last exact/ltRW/invR_gt0.
apply: mulR_ge0 => //; apply: mulR_ge0; first exact/sq_RV_ge0.
by rewrite /Ind; by case: ifPn.
Qed.

(* NB: not used *)
Lemma variance_nonneg (X : {RV P -> R}) : 0 <= `V X.
Proof. by have := cvariance_nonneg X setT; rewrite -Var_cVarT. Qed.

Lemma cresilience (delta : R) (X : {RV P -> R}) (F G : {set U}) :
  0 < delta -> delta <= Pr P F / Pr P G -> Pr P F < Pr P G -> F \subset G ->
    `| `E_[ X | F ] - `E_[ X | G ] | <=
    sqrt (`V_[ X | G ] * 2 * (1 - delta) / delta).
Proof.
move => delta_gt0 delta_FG Pr_FG /[dup] /setIidPr HGnF_F FG.
have HPrGpos : 0 < Pr P G by exact: (leR_ltR_trans _ Pr_FG).
have HPrFpos : 0 < Pr P F.
  apply/(@ltR_pmul2r (/ Pr P G)); first exact/invR_gt0.
  by rewrite mul0R; exact: (ltR_leR_trans _ delta_FG).
have delta_lt1 : delta < 1.
  by apply/(leR_ltR_trans delta_FG)/ltR_pdivr_mulr => //; rewrite mul1R.
case : (Rle_or_lt delta (1/2)) => delta_12.
(*Pr P F <= 1/2 , A.3 implies the desired result*)
  apply: (leR_trans (cEx_cVar _ _ _)) => //.
  apply sqrt_le_1_alt.
  rewrite !divRE -!mulRA; apply (leR_wpmul2l (cvariance_nonneg _ _)).
  apply: (@leR_trans (1/delta)).
    rewrite (leR_pdivl_mulr delta) //.
    rewrite mulRC -leR_pdivl_mulr; last exact: divR_gt0.
    rewrite div1R invRM ?gtR_eqF //; last exact: invR_gt0.
    by rewrite invRK ?gtR_eqF // mulRC.
  by rewrite !divRE mulRA leR_pmul2r; [lra|exact: invR_gt0].
rewrite cEx_Inv' //.
apply: leR_trans.
  apply leR_wpmul2l; first exact: divR_ge0.
  apply cEx_cVar => //; last exact: subsetDl.
  by rewrite Pr_diff HGnF_F subR_gt0.
apply: (@leR_trans
    (sqrt (`V_[ X | G] * (Pr P G * (1 - delta)) / (Pr P G * delta * delta)))).
  rewrite -(Rabs_pos_eq (Pr P (G :\: F) / Pr P F)); last exact: divR_ge0.
  rewrite -sqrt_Rsqr_abs; rewrite -sqrt_mult_alt; last exact: Rle_0_sqr.
  apply sqrt_le_1_alt.
  rewrite !divRE !mulRA [in X in X <= _](mulRC _  (`V_[X | G])) -!mulRA.
  apply: leR_wpmul2l; first exact: cvariance_nonneg.
  rewrite !mulRA mulRC !mulRA mulVR ?mul1R; last first.
    by rewrite Pr_diff HGnF_F; apply/eqP; nra.
  rewrite mulRC (mulRC (/Pr P F)) -mulRA -invRM; [|exact/gtR_eqF|exact/gtR_eqF].
  rewrite mulRA; apply/leR_pdivr_mulr; first by nra.
  rewrite mulRAC; apply/leR_pdivl_mulr; first by apply: Rmult_lt_0_compat; nra.
  move/leR_pdivl_mulr : delta_FG => /(_ HPrGpos) => delta_FG.
  apply Rmult_le_compat_r with (r:= Pr P G) in delta_FG => //.
  rewrite (mulRC (Pr P G)) -mulRA; apply: leR_pmul => //.
  - apply: mulR_ge0 => //; apply/mulR_ge0; last exact/ltRW.
    by apply/mulR_ge0 => //; exact/ltRW.
  - by rewrite Pr_diff HGnF_F; nra.
  - by rewrite mulRCA; apply: leR_pmul; nra.
apply sqrt_le_1_alt.
rewrite divRE invRM; [|exact/gtR_eqF/mulR_gt0|exact/gtR_eqF].
rewrite mulRA; apply/leR_pmul2r; first exact/invR_gt0.
rewrite -!mulRA; apply: leR_wpmul2l; first exact: cvariance_nonneg.
rewrite invRM; [|exact/gtR_eqF|exact/gtR_eqF].
rewrite mulRCA (mulRA (Pr P G)) mulRV ?mul1R; last exact/gtR_eqF.
rewrite mulRC; apply/leR_wpmul2r; first lra.
by rewrite -div1R; apply/leR_pdivr_mulr => //; nra.
Qed.

(* NB: not used, unconditional version of cresilience *)
Lemma resilience (delta : R) (X : {RV P -> R}) F :
  0 < delta -> delta <= Pr P F -> Pr P F < 1 ->
    `| `E_[ X | F ] - `E X | <= sqrt (`V X * 2 * (1 - delta) / delta).
Proof.
move=> delta_gt0 delta_F PF_lt1.
have := @cresilience _ X F setT delta_gt0.
rewrite Pr_setT divR1 => /(_ delta_F PF_lt1); rewrite -Ex_cExT -Var_cVarT.
by apply; exact/subsetT.
Qed.

Infix ">=?" := Rgeb : R_scope.

Lemma Ind_one F : Pr P F <> 0 -> `E_[Ind F : {RV P -> R} | F] = 1.
Proof.
move=> F0; rewrite cEx_ExInd.
have -> : Ind F `* Ind F = Ind F.
  by rewrite /Ind boolp.funeqE => u; case: ifPn; rewrite ?(mulR0,mulR1).
by rewrite E_Ind divRE mulRV//; exact/eqP.
Qed.
Arguments Ind_one : clear implicits.

Theorem robust_mean (good drop: {set U}) (X : {RV P -> R}) (eps : R):
  let bad := ~: good in
  let mu_hat := `E_[ X | ~: drop ] in
  let mu := `E_[ X | good ] in
  let sigma := `V_[ X | good ] in
  0 < eps -> eps <= 1/8 ->
  Pr P bad = eps -> Pr P drop = 4 * eps ->
  (* All the outliers exceeding the ε-quantile are eliminated: *)
  (forall y, y \in bad -> sqrt (sigma / eps) < `| X y - mu | -> y \in drop) ->
  `| mu_hat - mu | <=  8 * sqrt (sigma / eps).
Proof.
move=> bad mu_hat mu sigma Hmin_outliers Hmax_outliers Hbad_ratio Hdrop_ratio
  Hquantile_drop_bad.
have H : Pr P good = 1 - eps by apply/esym/subR_eq; rewrite -Hbad_ratio Pr_cplt.
(* On the other hand, we remove at most 4ε good points *)
have max_good_drop : Pr P (good :&: drop) <= 4 * eps.
  by rewrite -Hdrop_ratio; exact/Pr_incl/subsetIr.
pose eps' := Pr P (bad :\: drop) / Pr P (~: drop).
have Hcompl : Pr P (good :\: drop) / Pr P (~: drop) = 1 - eps'.
  apply/esym/subR_eq; rewrite /eps' -mulRDl -Pr_union_disj.
    by rewrite -setDUl setUCr setTD mulRV// Pr_of_cplt; apply/eqP; lra.
  by rewrite -setI_eq0 -setDIl setICr set0D.
have eps'_ge0 : 0 <= eps'.
  by apply: mulR_ge0 => //; apply/ltRW/invR_gt0; rewrite Pr_of_cplt; lra.
have eps'_le1 : eps' <= 1.
  rewrite /eps'; apply/leR_pdivr_mulr; first by rewrite Pr_of_cplt; lra.
  by rewrite mul1R; exact/Pr_incl/subsetDr.
(* Remaining good points: 1 - (4 * eps) / (1 - eps) *)
pose delta := 1 - (4 * eps) / (1 - eps).
have min_good_remain : delta <= Pr P (good :\: drop) / Pr P good.
  rewrite /delta Pr_diff H.
  apply: (@leR_trans ((1 - eps - 4 * eps) / (1 - eps))).
    apply/leR_pdivl_mulr; first lra.
    by rewrite mulRDl -mulNR -(mulRA _ (/ _)) Rinv_l; lra.
  apply/leR_pdivr_mulr; first lra.
  rewrite -[X in _ <= X]mulRA mulVR ?mulR1; first lra.
  by apply/eqP; lra.
have delta_gt0 : 0 < delta.
  apply (@ltR_pmul2r (1 - eps)); first lra.
  by rewrite mul0R mulRDl mul1R -mulNR -mulRA Rinv_l; lra.
have delta_le1 : delta <= 1.
  apply (@leR_pmul2r (1 - eps)); first lra.
  by rewrite mul1R mulRDl mul1R -mulNR -mulRA Rinv_l ?mulR1; lra.
have Exgood_bound : `| `E_[X | good :\: drop ] - `E_[X | good] | <=
                     sqrt (`V_[X | good] * 2 * (1 - delta) / delta).
  have [gdg|gdg] := eqVneq (Pr P (good :\: drop)) (Pr P good).
  - suff : `E_[X | (good :\: drop)] = `E_[X | good].
      by move=> ->; rewrite subRR normR0; exact: sqrt_pos.
    apply: eq_bigr => i _; rewrite gdg; congr (_ * _ * _).
    rewrite setIDA Pr_diff -setIA.
    (* NB: lemma? *)
    apply/subR_eq; rewrite addRC; apply/subR_eq; rewrite subRR; apply/esym.
    move: gdg; rewrite Pr_diff => /subR_eq; rewrite addRC => /subR_eq.
    by rewrite subRR [in X in _ -> X]setIC => /esym; exact: Pr_domin_setI.
  - apply cresilience.
    + apply (@ltR_pmul2r (1 - eps)); first lra.
      by rewrite mul0R; apply: mulR_gt0 => //; lra.
    + lra.
    + suff : Pr P (good :\: drop) <= Pr P good by move/eqP in gdg; lra.
      exact/Pr_incl/subsetDl.
    + exact: subsetDl.
have Exbad_bound : 0 < Pr P (bad :\: drop) ->
    `| `E_[ X | bad :\: drop ] - mu | <= sqrt (sigma / eps).
  move=> Pr_bd.
  rewrite -(mulR1 mu) -(Ind_one (bad :\: drop)); last lra.
  rewrite 2!cEx_ExInd -addR_opp -mulNR mulRA -I_double -mulRDl big_distrr /=.
  rewrite /Ex -big_split /= [X in `|X */ _|](_ : _ =
      \sum_(i in U) (X i - mu) * @Ind U (bad :\: drop) i * P i); last first.
    by apply: eq_bigr => u _; rewrite -mulRA mulNR addR_opp -mulRBl mulRA.
  rewrite normRM (geR0_norm (/ _)); last exact/ltRW/invR_gt0.
  apply/leR_pdivr_mulr => //; apply: (leR_trans (leR_sumR_Rabs _)).
  rewrite (bigID [pred i | i \in bad :\: drop]) /=.
  rewrite [X in _ + X]big1 ?addR0; last first.
    by move=> u /negbTE abaddrop; rewrite /Ind abaddrop mulR0 mul0R normR0.
  rewrite /Pr big_distrr /=; apply leq_sumR => i ibaddrop.
  rewrite normRM (geR0_norm (P i))//; apply: leR_wpmul2r => //.
  rewrite /Ind ibaddrop mulR1.
  move: ibaddrop; rewrite inE => /andP[idrop ibad].
  by rewrite leRNgt => /Hquantile_drop_bad => /(_ ibad); apply/negP.
have max_bad_remain : Pr P (bad :\: drop) <= eps / Pr P (~: drop).
  rewrite Pr_of_cplt Hdrop_ratio Pr_diff Hbad_ratio.
  apply: (@leR_trans eps); first exact/leR_subl_addr/leR_addl.
  by apply/leR_pdivl_mulr; [lra|nra].
have Ex_not_drop : `E_[ X | ~: drop ] =
    (`E_[ X | good :\: drop ] * Pr P (good :\: drop) +
     `E_[ X | bad :\: drop ] * Pr P (bad :\: drop))
    / Pr P (~: drop).
  have good_bad : Pr P (good :\: drop) + Pr P (bad :\: drop) = Pr P (~: drop).
    rewrite -(_ : good :\: drop :|: bad :\: drop = ~: drop); last first.
      by rewrite -setDUl setUCr setTD.
    rewrite Pr_union_eq.
    apply/subR_eq; rewrite subR_opp addRC; apply/esym/subR_eq; rewrite subRR.
    suff : (good :\: drop) :&: (bad :\: drop) = set0.
      by move=> ->; rewrite Pr_set0.
    by rewrite !setDE setIACA setIid setICr set0I.
  have [bd0|/eqP bd0 {good_bad}] := eqVneq (Pr P (bad :\: drop)) 0.
  - rewrite bd0 addR0 in good_bad.
    rewrite bd0 mulR0 addR0 good_bad.
    rewrite /Rdiv -mulRA mulRV ?mulR1; last first.
      by apply/Pr_gt0; rewrite -good_bad Pr_diff H; lra.
    rewrite 2!cEx_ExInd good_bad; congr (_ / _).
    apply/eq_bigr => u _.
    rewrite /ambient_dist -!mulRA; congr (_ * _).
    (* NB: lemma? *)
    rewrite /Ind !inE.
    have bad_drop0 : u \in bad :\: drop -> P u = 0 by apply Pr_set0P.
    case: ifPn => idrop //=.
    by case: ifPn => // igood; rewrite bad_drop0 ?mulR0// !inE idrop.
  - apply/eqR_divl_mulr; first by rewrite Pr_of_cplt; apply/eqP; nra.
    rewrite !cEx_ExInd -!mulRA.
    rewrite Rinv_l ?mulR1; last by rewrite Pr_of_cplt; nra.
    rewrite Rinv_l ?mulR1; last nra.
    rewrite Rinv_l // mulR1.
    rewrite [in RHS]/Ex -big_split; apply: eq_bigr => i _ /=.
    rewrite /ambient_dist -!mulRA -mulRDr -mulRDl ; congr (X i * (_ * _)).
    (* NB: lemma? *)
    rewrite /Ind !inE; case: ifPn => //=; rewrite ?(addR0,add0R)//.
    by case: ifPn => //=; rewrite ?(addR0,add0R).
rewrite -(mulR1 mu).
rewrite (_ : 1 = eps' + Pr P (good :\: drop) / Pr P (~: drop)); last first.
  by rewrite Hcompl addRCA addR_opp subRR addR0.
rewrite (mulRDr mu) -addR_opp oppRD.
rewrite /mu_hat Ex_not_drop divRDl.
rewrite {2}/Rdiv -(mulRA `E_[X | _]) -divRE -/eps'.
rewrite Hcompl.
rewrite {1}/Rdiv -(mulRA `E_[X | _]) -divRE.
rewrite Hcompl.
rewrite -addRA addRC addRA -!mulNR -(mulRDl _ _ eps').
rewrite -addRA -mulRDl.
rewrite (addRC (-mu)).
apply: (leR_trans (Rabs_triang _ _)).
rewrite 2!normRM (geR0_norm eps'); last lra.
rewrite (geR0_norm (1 - eps')); last lra.
apply: (@leR_trans (sqrt (`V_[ X | good] / eps) * eps' +
    sqrt (`V_[ X | good] * 2 * (1 - delta) / delta) * (1 - eps'))).
  have [->|/eqP eps'0] := eqVneq eps' 0.
    by rewrite !(mulR0,add0R,subR0,mulR1).
  have [->|/eqP eps'1] := eqVneq eps' 1.
    rewrite !(subRR,mulR0,addR0,mulR1); apply: Exbad_bound.
    apply Pr_gt0; apply: contra_notN eps'0 => /eqP.
    by rewrite /eps' => ->; rewrite div0R.
  have [bd0|bd0] := eqVneq (Pr P (bad :\: drop)) 0.
    by exfalso; apply/eps'0; rewrite /eps' bd0 div0R.
  apply: leR_add; (apply/leR_pmul2r; first lra).
  - exact/Exbad_bound/Pr_gt0.
  - exact: Exgood_bound.
rewrite /sigma /Rdiv !sqrt_mult //; last 8 first.
  - by apply: cvariance_nonneg; lra.
  - lra.
  - by apply: mulR_ge0; [apply: cvariance_nonneg; lra|lra].
  - lra.
  - apply: mulR_ge0; [|lra].
    by apply: mulR_ge0; [apply: cvariance_nonneg; lra|lra].
  - by apply/ltRW/invR_gt0; lra.
  - by apply: cvariance_nonneg; lra.
  - by apply/ltRW/invR_gt0; lra.
rewrite (mulRC 8) -!mulRA -mulRDr; apply: leR_wpmul2l; first exact: sqrt_pos.
rewrite mulRA -sqrt_mult; [|lra|lra].
rewrite mulRA -sqrt_mult; [|lra|]; last by apply/ltRW/invR_gt0; lra.
rewrite addRC; apply/leR_subr_addr.
rewrite -mulRBr -(sqrt_Rsqr (1 - eps')); last lra.
rewrite -(sqrt_Rsqr (8 - eps')); last lra.
rewrite -sqrt_mult; last 2 first.
  - by apply/mulR_ge0; [lra|apply/ltRW/invR_gt0; lra].
  - exact: Rle_0_sqr.
rewrite -sqrt_mult; last 2 first.
  - by apply/ltRW/invR_gt0; lra.
  - exact: Rle_0_sqr.
apply/sqrt_le_1_alt/leR_pmul.
- by apply: mulR_ge0; [lra|apply/ltRW/invR_gt0; lra].
- exact: Rle_0_sqr.
- rewrite -divRE; apply/leR_pdivr_mulr; first lra.
  rewrite (mulRC _ delta) -divRE; apply/leR_pdivl_mulr; first lra.
  rewrite mulRC mulRA; apply/(@leR_pmul2r (1 - eps)); first lra.
  rewrite mulRDl mul1R -mulNR -(mulRA _ (/ _)) Rinv_l ?mulR1; last lra.
  by rewrite -mulRA mulRDl oppRD oppRK mulRDl -(mulRA _ (/ _)) Rinv_l; [nra|lra].
- by apply/Rsqr_incr_1; lra.
Qed.

Lemma cEx_add_RV (X Y : {RV (P) -> (R)}) F:
  `E_[(X `+ Y) | F] = `E_[X | F] + `E_[Y | F].
Proof.
  rewrite !cEx_ExInd -mulRDl.
  congr (_ * _).
  rewrite -E_add_RV.
  apply congr_big => // i HiU.
  by rewrite mulRDl.
Qed.

Lemma cEx_sub_RV (X Y: {RV P -> R}) F: `E_[X `- Y | F] = `E_[X|F] - `E_[Y|F].
Proof.
  rewrite !cEx_ExInd.
  unfold Rminus.
  rewrite -mulNR.
  rewrite big_morph_oppR -mulRDl.
  congr (_ * _).
  rewrite -big_split /=.
  apply eq_bigr => u _.
  by rewrite -mulNR -mulRDl -mulNR -mulRDl.
Qed.

Lemma cEx_const_RV (k : R_eqType) F:
  0 < Pr P F ->
  `E_[(const_RV P k) | F] = k.
Proof.
  move => HPrPF.
  by rewrite cEx_ExInd E_scalel_RV E_Ind /Rdiv -mulRA mulRV; [rewrite mulR1 | apply gtR_eqF].
Qed.

Lemma const_RC (X: {RV P -> R}) k: X `*cst k = k `cst* X.
Proof.
  unfold "`*cst", "`cst*".
  rewrite boolp.funeqE => x.
  by rewrite mulRC.
Qed.

Lemma cEx_scaler_RV (X : {RV (P) -> (R)}) (k : R) F:
  `E_[(X `*cst k) | F] = `E_[X | F] * k.
Proof.
  rewrite !cEx_ExInd mulRC mulRA.
  congr (_ * _).
  rewrite -E_scalel_RV const_RC.
  apply eq_bigr => i _.
  unfold "`cst*".
  by rewrite mulRA.
Qed.

Lemma cEx_scalel_RV (X : {RV (P) -> (R)}) (k : R) F:
  `E_[(k `cst* X) | F] = k * `E_[X | F].
Proof.
  by rewrite mulRC -cEx_scaler_RV const_RC.
Qed.

Lemma cEx_trans_add_RV (X: {RV P -> R}) m F: 
0 < Pr P F ->
  `E_[X `+cst m | F] = `E_[X | F] + m.
Proof.
  move => HPrPF_gt0.
  have: `E_[const_RV P m | F] = m by apply cEx_const_RV.
  move => HcExm.
  by rewrite -{2}HcExm -cEx_add_RV.
Qed.

Lemma cEx_trans_RV_id_rem (X: {RV P -> R}) m F:
  `E_[(X `-cst m) `^2 | F] = `E_[((X `^2 `- (2 * m `cst* X)) `+cst m ^ 2) | F].
Proof.
  rewrite !cEx_ExInd.
  congr (_ * _).
  apply eq_bigr => a _.
  rewrite /sub_RV /trans_add_RV /trans_min_RV /sq_RV /= /comp_RV /scalel_RV /=.
  by rewrite /ambient_dist; field.
Qed.

Lemma cEx_Pr_eq0 (X: {RV P -> R}) F:
  Pr P F = 0 -> `E_[X | F] = 0.
Proof.
  move => HPrF0.
  apply psumR_seq_eq0P => [|a _| a _];
  first apply undup_uniq;
  by rewrite product_rule HPrF0 !mulR0 /Rdiv mul0R; try right.
Qed.

Lemma cVarE (X : {RV (P) -> (R)}) F:
  `V_[X | F] = `E_[X `^2 | F] - `E_[X | F] ^ 2.
Proof.
  have: 0 <= Pr P F by apply Pr_ge0.
  case => [HPr_gt0 | HPr_eq0].
    rewrite /cVar cEx_trans_RV_id_rem.
    rewrite cEx_trans_add_RV; last by [].
    rewrite cEx_sub_RV cEx_scalel_RV.
    field.
  by rewrite /cVar !cEx_Pr_eq0; first (simpl; rewrite mul0R subR0).
Qed.

Lemma cVarDist (X : {RV P -> R}) F x:
  0 < Pr P F ->
  `E_[(X `-cst x) `^2 | F] =
    `V_[X | F] + (`E_[X | F] - x)².
Proof.
  move => HPrPF.
  unfold Rsqr.
  rewrite cVarE.
  simpl; rewrite mulR1 mulRDl !mulRDr !addRA -(mulRC (- _)) -!addRA addRA addRA -(addRA _ (- _)) (addRC (- _)).
  have ->:  `E_[X | F] * `E_[X | F] + - (`E_[X | F] * `E_[X | F]) = 0 by apply subRR.
  rewrite addR0 -!cEx_scalel_RV.
  have <-: `E_[(const_RV P (-x * -x)) | F] = (-x * -x) by apply cEx_const_RV.
  rewrite -!cEx_add_RV !cEx_ExInd.
  congr (_ * _).
  apply eq_bigr => i _.
    repeat congr (_ * _);
    unfold "`-cst", "`^2", "`o", "`cst*", const_RV, "`+";
    simpl.
    by rewrite !mulR1 mulRDl !mulRDr !addRA -(mulRC (-_)).
Qed.

Variable X : {RV P -> R}.
Variable good : {set U}.
Variable eps : R.
Definition C0 (i: U) := 1.
Definition bad := ~: good.
Definition mu := `E_[X | good].
Definition var := `V_[X | good].
Definition mu_hat C := (\sum_(i in U) P i * C i * X i) / (\sum_(i in U) P i * C i).
Definition tau C := (X `-cst mu_hat C)`^2.
Definition var_hat C := (\sum_(i in U) P i * C i * tau C i) / (\sum_(i in U) P i * C i).

Lemma eqn1_1 (C: U -> R):
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

Definition tau_max C := \rmax_(i in [set: U]) tau C i.

Definition update (C: U -> R) :=
  fun i => C i * (1 - tau C i / tau_max C).

Definition invariant (C: U -> R) :=
  (\sum_(i in good) P i * (1 - C i) <= (1 - eps)/2 * \sum_(i in bad) P i * (1 - C i)).
Definition invariant1 C :=
  (1 - eps <= (\sum_(i in good) P i * C i) / (\sum_(i in U) P i * C i)).
Definition weight (C: U -> R) :=
  (forall i, 0 <= C i <= 1).

Lemma base_case: Pr P bad = eps -> invariant C0 /\ invariant1 C0 /\ weight C0.
Proof.
  move => Hbad_ratio.
  rewrite /invariant.
  apply conj.
    under eq_bigr => i _. rewrite subRR mulR0. over.
    rewrite big1; last by [].
    under eq_bigr => i _. rewrite subRR mulR0. over.
    rewrite big1; last by [].
    rewrite Rmult_0_r. apply leRR.
  apply conj.
  rewrite /invariant1.
  have ->: (\sum_(i in good) P i * C0 i) = Pr P good
    by under eq_bigr => i _; [rewrite /C0 mulR1; over|].
  have ->: (\sum_(i in U) P i * C0 i) = 1.
    under eq_bigr => i _. rewrite /C0 mulR1. over.
    rewrite sumR_setT -(Pr_setT P) /Pr.
    apply eq_bigl => x.
    by rewrite Bool.andb_true_r.
    have -> : Pr P good = 1 - eps by apply/esym/subR_eq; rewrite -Hbad_ratio Pr_cplt.
    by rewrite divR1 leR_eqVlt; left.
  move => i. rewrite /C0; lra.
Qed.

Lemma lemma1_4_start C:
  0 < \sum_(i in U) P i * C i ->
  Pr P bad = eps ->
  eps < 1 ->
  weight C -> invariant C -> invariant1 C.
Proof.
  rewrite /weight/invariant/invariant1 => HCi_gt0 HPr_bad Heps HwC HIC.
  have HPr_good: Pr P good = 1 - eps.
    by rewrite -HPr_bad Pr_of_cplt subRB subRR add0R.
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

Definition mu_wave C := (\sum_(i in good) P i * C i * X i) / (\sum_(i in good) P i * C i).

Lemma lemma_1_4_step1 C:
  Pr P bad = eps ->
  Rsqr (mu_hat C - mu_wave C) <= `V_[X | good] * 2*eps / (1-eps).
Proof.
  move => HPr_bad.
  rewrite /mu_hat /mu_wave.
Admitted.

Lemma eqn1_3_4 C (S: {set U}):
  let C' := update C in
  \sum_(i in S) P i * (1 - C' i) =
    (\sum_(i in S) P i * (1 - C i)) + 1 / tau_max C * (\sum_(i in S ) P i * (C i * tau C i)).
Proof.
  move => C'.
  have <-: \sum_(i in S) P i * (C i - C' i) = 1 / tau_max C * (\sum_(i in S) P i * (C i * tau C i)).
    rewrite /C' /update big_distrr.
    apply eq_bigr => i _. simpl.
    by rewrite /Rminus /Rdiv (mulRDr (C i)) mulR1 oppRD addRA mulRN oppRK addRN add0R !mulRA !mulR1 mul1R mulRC !mulRA.
  rewrite -big_split.
  apply eq_bigr => i HiS. simpl.
  rewrite -mulRDr. congr (_*_). lra.
Qed.

Lemma lemma_1_5 C:
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

Definition filter1d gas :=
  let fix filter1d_iter gas C := match gas with
    0      => None
  | S gas' => if Rleb (var_hat C) var then Some (mu_hat C) else filter1d_iter gas' (update C)
  end in filter1d_iter gas C0.


Lemma first_note (good: {set U}) (C: U -> R) eps:
  invariant good C eps -> 1 - eps <= (\sum_(i in good) C i * P i) / (\sum_(i in U) C i * P i).
Admitted.

Lemma lemma_1_4_step1 (good: {set U}) (X: {RV P -> R}) (C: U -> R) eps:
let bad := ~: good in
let mu_hat_c := (\sum_(i in U) C i * X i) / (\sum_(i in U) C i) in
let mu := `E_[X | good] in
let var := `V_[X | good] in
let tau := (X `-cst mu_hat_c)`^2 in
let var_hat_c := (\sum_(i in U) C i * tau i) / (\sum_(i in U) C i) in (*added*)
Pr P bad = eps ->
0 < eps <= 1/12 ->
var_hat_c >= 16 * var -> (*added*)
(forall a, 0 <= C a <= 1) -> `| mu - mu_hat_c | <= sqrt(var*2*eps/(2-eps)) + sqrt(var_hat_c*2*eps/(1-eps)).
Admitted.

End probability.

Require Import List.
Require Import Sorting.
Require Orders.

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
Recursive Extraction TrimmedMean.
