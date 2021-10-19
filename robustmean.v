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

Section RV_ring.
Variables (U : finType) (P : fdist U).
Import topology.
Import GRing.Theory.

Lemma add_RV_addr (X Y : {RV P -> R}) : X `+ Y = GRing.add X Y.
Proof. reflexivity. Qed.

Lemma sub_RV_subr (X Y : {RV P -> R}) : X `- Y = (GRing.add X (GRing.opp Y)).
Proof. reflexivity. Qed.

Lemma trans_min_RV_subr (X : {RV P -> R}) (y : R) :
  X `-cst y = GRing.add X (GRing.opp (cst y)).
Proof. reflexivity. Qed.

Definition fdist_supp_choice : U.
by move/set0Pn/xchoose:(fdist_supp_neq0 P).
Defined.

Canonical fdist_supp_pointedType :=
  @classical_sets.Pointed.pack U fdist_supp_choice _ _ idfun.

Lemma mul_RV_mulr (X Y : {RV P -> R}) : X `* Y = GRing.mul X Y.
Proof. reflexivity. Qed.

Lemma sq_RV_sqrr (X : {RV P -> R}) : X `^2 = GRing.exp X 2.
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
move/subsetP=> YsubX; rewrite /Ind /sub_RV; apply boolp.funext=> u /=.
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

Lemma variance_nonneg (X : {RV P -> R}) : 0 <= `V X.
Proof.
by apply: sumR_ge0 => u _; apply mulR_ge0 => //; apply: sq_RV_ge0.
Qed.

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
rewrite Ind_setD //.
have -> : forall A B C, A `* (B `- C) = (A `* B) `- (A `* C)
    by move=> V P0 P1 A B C; apply boolp.funext=> v; rewrite mulRDr mulRN.
rewrite E_sub_RV.
have -> : Ex P ((X `-cst `E_[X | G]) `* Ind G) = 0.
  apply normR0_eq0.
  by rewrite -(@eqR_mul2r (/ Pr P G)) // -divRE -cEx_sub // subRR normR0 mul0R.
rewrite sub0R normRN.
by rewrite [X in _ = _ * X]mulRAC mulRV // mul1R.
Qed.

Lemma cEx_Inv (X: {RV P -> R}) F :
  0 < Pr P F -> Pr P F < 1 ->
  `| `E_[X | F] - `E X| = (1 - Pr P F) / Pr P F * `| `E_[X | (~: F)] - `E X|.
Proof.
move=> *; rewrite Ex_cExT -Pr_of_cplt -setTD; apply cEx_Inv' => //.
apply ltR_neqAle; split; last by apply/Pr_incl/subsetT.
by apply/eqP; rewrite Pr_setT -Pr_lt1.
Qed.

Lemma resilience (delta: R) (X : {RV P -> R}) F:
  0 < delta -> delta <= Pr P F -> Pr P F < 1 ->
    `| `E_[ X | F ] - `E X | <= sqrt (`V X * 2 * (1-delta) / delta).
Proof.
  move => H H0 H1.
  have: delta <= 1/2 \/ 1/2 < delta by apply Rle_or_lt.
  case => [H2|H2].
  { (*Pr P F <= 1/2 , A.3 implies the desired result*)
    apply leR_trans with (y := sqrt (`V X / Pr P F )).
    apply cEx_Var. lra.
    apply sqrt_le_1_alt. unfold Rdiv.
    repeat rewrite -> Rmult_assoc.
    apply Rmult_le_compat_l.
    apply variance_nonneg. 

    rewrite <- Rmult_1_l at 1.
    rewrite -Rmult_assoc. 
    apply leR_pmul; try (apply/Rlt_le/invR_gt0); try lra.
    by apply leR_inv.
  }

  { (*Prob > 1/2 and delta < Probability*)
    rewrite cEx_Inv.
    (*Search (?x <= ?y -> ?y <= ?z -> ?x <= ?z).*)
    apply Rle_trans with (r2 := ((1 - Pr P F) / Pr P F * sqrt (`V X / Pr P (~: F)))).
    have H3: 0 < Pr P F by lra.
    
    apply Rmult_le_compat_l.
    - apply divR_ge0; lra.
    - apply cEx_Var; rewrite Pr_of_cplt; lra.
    
    - (*(1 - Pr P F) / Pr P F * sqrt (`V X / Pr P (~: F)) <=
    sqrt (`V X * 2 * (1 - delta) / delta)*) 
    rewrite -(Rabs_pos_eq ((1 - Pr P F) / Pr P F )).
    rewrite -sqrt_Rsqr_abs;
    rewrite -sqrt_mult_alt.
    apply sqrt_le_1_alt;
    (*((1 - Pr P F) / Pr P F)² * (`V X / Pr P (~: F)) <=
`V X * 2 * (1 - delta) / delta*)
    (*Search (?x / ?y = ?x * _).*)
    repeat rewrite divRE;
    rewrite -Rmult_assoc;
    (*Search (?x * ?y  = ?y * ?x ).*)
    rewrite (Rmult_comm ((1 - Pr P F) * / Pr P F)²  (`V X));
    (*rewrite (Rmult_assoc (`V X ) (2 * (1 - delta) * / delta)).*)
    (*Search (?x * _ <= ?x * _).*)
    (*Set Printing All.*)
    repeat rewrite Rmult_assoc;
    (*rewrite (Rmult_assoc (`V X ) (2 * (1 - delta) * / delta)).*)
    apply Rmult_le_compat_l. 

    apply variance_nonneg.

    rewrite Pr_of_cplt; 
    rewrite (Rmult_comm (/ Pr P F) (/ (1 - Pr P F)));
    rewrite -(Rmult_assoc (1 - Pr P F) (/ (1 - Pr P F)));
    (*Search (/?x * ?x).*)
    rewrite Rinv_r.
    (*Search (1 * _).*)
    rewrite Rmult_1_l;
    (*Search (?x * ?x).
    Search (_ * ?x <= _ * ?x).*)
    apply Rmult_le_reg_r with (r := delta).

    assumption.

    repeat rewrite Rmult_assoc;
    rewrite Rinv_l.
    rewrite mulR1;
    apply Rmult_le_reg_r with (r := (Pr P F * Pr P F)). nra.
    
    repeat rewrite Rmult_assoc;
    rewrite (Rmult_comm (delta));
    rewrite  (Rmult_assoc (Pr P F));
    rewrite -(Rmult_assoc (/ Pr P F ) (Pr P F));
    rewrite Rinv_l.
    rewrite Rmult_1_l;
    rewrite -(Rmult_assoc (/ Pr P F));
    rewrite Rinv_l.
    rewrite Rmult_1_l. 

    (*Search (?x * ?y <= ?z * ?u).*)
    repeat rewrite -Rmult_assoc;
    apply Rmult_le_compat.

    all: try lra. nra.

    - apply Rle_0_sqr.
    - apply divR_ge0; try lra.
   (*THE END*)
  }

Qed.

Lemma cvariance_nonneg (X : {RV P -> R}) F : 0 < Pr P F -> 0 <= `V_[X | F].
(* note: we could drop 0 < Pr P F *)
Proof.
  move => H.
  unfold cVar.
  rewrite cEx_EXInd.
  unfold Ex, ambient_dist.
  rewrite divRE big_distrl /=. 
  apply sumR_ge0. intros.
  rewrite /sq_RV/comp_RV/=.
  unfold "^".
  apply mulR_ge0.
    rewrite mulR1.
    apply mulR_ge0 .
      apply mulR_ge0.
        by apply Rle_0_sqr.
      unfold Ind.
      by destruct (i \in F) eqn:H1; rewrite H1; lra.
    by apply FDist.ge0.
  apply/Rlt_le/Rinv_0_lt_compat.
  by auto.
Qed.

Lemma resilience' (delta: R) (X : {RV P -> R}) (F G: {set U}):
  0 < delta -> delta <= Pr P F / Pr P G -> Pr P F < Pr P G -> F \subset G ->
    `| `E_[ X | F ] - `E_[ X | G ] | <= sqrt (`V_[ X | G ] * 2 * (1-delta) / delta).
Proof.
  move => H H0 H1 H2.
  have HPrGpos : 0 < Pr P G.
    apply Rle_lt_trans with (r2 := Pr P F).
      by apply Pr_ge0.
      by auto.
  have HPrFpos : 0 < Pr P F.
    apply Rlt_le_trans with (r2 := delta * Pr P G).
      by apply Rmult_lt_0_compat; lra.
      apply Rmult_le_reg_r with (r := / Pr P G).
        apply Rinv_0_lt_compat; auto.
      rewrite Rmult_assoc Rinv_r.
        by rewrite mulR1. 
      by lra.
    
  have HGnF_F : G :&: F = F.
    apply: setIidPr.
    by auto.
    
  have Hdelta_pos : delta < 1.
    apply Rmult_le_compat_r with (r:= Pr P G) in H0.
      rewrite Rmult_assoc in H0.
      rewrite Rinv_l in H0.
        rewrite mulR1 in H0. by nra. 
      by nra. 
    by nra.
      
    case H3 : (Rle_or_lt delta (1/2)).
    (*Pr P F <= 1/2 , A.3 implies the desired result*)
      apply leR_trans with (y := sqrt (`V_[X | G] * Pr P G / Pr P F )).
      apply cEx_cVar. nra. auto.
      apply sqrt_le_1_alt. unfold Rdiv.
      repeat rewrite -> Rmult_assoc.
      apply Rmult_le_compat_l.
        apply cvariance_nonneg. by auto.
      apply Rle_trans with (r2 := 1/delta).
        apply Rmult_le_reg_r with (r := delta * Pr P F / Pr P G).
          by nra.
      unfold Rdiv.
      repeat rewrite -Rmult_assoc.
      have H4 : (Pr P G * / Pr P F * delta * Pr P F * / Pr P G =
      delta * (Pr P G * / Pr P G) * (Pr P F * / Pr P F)).
        by lra.
      rewrite H4.
          repeat rewrite Rinv_r; repeat rewrite mulR1.
          rewrite Rmult_1_l Rinv_l .
            rewrite Rmult_1_l.
            all: try lra.
      apply Rmult_le_reg_r with (r:= delta).
        by lra.
      repeat rewrite Rmult_assoc.
      repeat rewrite Rinv_l.
      lra.
      lra.
    }
    { (* Prob > 1/2 and delta < Probability *)
      rewrite cEx_Inv'.
      apply Rle_trans with (r2 := Pr P (G :\: F) / Pr P F * sqrt (`V_[X | G] * Pr P G / Pr P (G :\: F))).
      
      apply Rmult_le_compat_l.
      - apply divR_ge0. rewrite Pr_diff. rewrite HGnF_F. lra. lra.
      - apply cEx_cVar. rewrite Pr_diff. rewrite HGnF_F. lra. apply subsetDl.
      
          apply Rle_trans with (r2 := sqrt (`V_[ X | G] * (Pr P G * (1 - delta)) / (Pr P G * delta * delta))).
            rewrite -(Rabs_pos_eq (Pr P (G :\: F) / Pr P F)).
              rewrite -sqrt_Rsqr_abs; rewrite -sqrt_mult_alt.
                apply sqrt_le_1_alt. 
                unfold Rdiv.
                repeat rewrite -Rmult_assoc.
                rewrite (Rmult_comm _  (`V_[X | G])).
                repeat rewrite Rmult_assoc; apply Rmult_le_compat_l. 
                  apply cvariance_nonneg. by auto.

                repeat rewrite -Rmult_assoc.
                rewrite Rmult_comm.
                repeat rewrite -Rmult_assoc.
                rewrite Rinv_l.
                  rewrite Rmult_1_l Rmult_comm (Rmult_comm (/Pr P F)) Rmult_assoc -Rinv_mult_distr .
                    rewrite -Rmult_assoc.
                    apply Rmult_le_reg_r with (r:=Pr P F * Pr P F).
                      by nra.
                    rewrite Rmult_assoc Rinv_l.
                      rewrite mulR1 Rmult_assoc (Rmult_comm (/ _)) -Rmult_assoc.
                      apply Rmult_le_reg_r with (r:= Pr P G * delta * delta).
                        apply Rmult_lt_0_compat.
                          by nra. 
                        by lra.
                      rewrite (Rmult_assoc _ (/ _)) Rinv_l .
                        rewrite mulR1.
                        apply Rmult_le_compat_r with (r:= Pr P G) in H0.
                          rewrite Rmult_assoc in H0 .
                          rewrite Rinv_l in H0.
                            rewrite mulR1 in H0.
                            rewrite (Rmult_comm (Pr P G)) Rmult_assoc.
                            apply Rmult_le_compat.
                                  by apply Pr_ge0.
                                by nra.
                              rewrite Pr_diff HGnF_F.
                              apply Rle_trans with (r2:=Pr P G - delta * Pr P G).
                                by nra.
                              by nra.
                            rewrite Rmult_comm Rmult_assoc (Rmult_comm (delta)).
                            apply Rmult_le_compat.
                              all: try nra.
              repeat apply Rmult_integral_contrapositive_currified; by nra.
            rewrite Pr_diff HGnF_F. by nra.
          by apply Rle_0_sqr.
        rewrite Pr_diff HGnF_F.
        apply/Rlt_le/Rmult_lt_0_compat.
          by nra.
        apply Rinv_0_lt_compat.
        by nra.
      apply sqrt_le_1_alt.
      rewrite divRE Rinv_mult_distr.
          rewrite -Rmult_assoc.
          apply Rmult_le_compat_r.
            apply/Rlt_le/Rinv_0_lt_compat.
            by lra.
          repeat rewrite Rmult_assoc.
          apply Rmult_le_compat_l.
            apply cvariance_nonneg. by lra.
          rewrite Rinv_mult_distr.
              rewrite -Rmult_assoc (Rmult_comm (Pr P G)) -Rmult_assoc (Rmult_assoc (1 - delta)) Rinv_r .
                rewrite mulR1 (Rmult_comm 2).
                repeat rewrite Rmult_assoc.
                apply Rmult_le_compat_l.
                all: try nra.
    apply Rmult_le_reg_r with (r:=delta).
      by lra.
    rewrite Rinv_l.
      by lra.
    by nra.
  by auto.
Qed.

Infix ">=?" := Rgeb : R_scope.

Lemma Ind_one F :
  Pr P F <> 0 -> `E_[Ind F : {RV P -> R} | F] = 1.
Proof.
  move => H.
  rewrite cEx_EXInd.
  have I_mult : (Ind F `* Ind F = Ind F). 
    apply boolp.funext=> u.
    unfold Ind.
    by case : ifPn; nra.
  by rewrite I_mult E_Ind divRE Rinv_r //.
Qed.
Arguments Ind_one : clear implicits.

Theorem robust_mean
  (good drop: {set U})
  (X: {RV P -> R})
  (eps: R):
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
have H : Pr P good = 1 - eps.
  rewrite -[RHS]oppRK -[LHS]oppRK; congr (- _); apply/(Rplus_eq_reg_l 1).
  by rewrite addR_opp -Pr_of_cplt Hbad_ratio; nra.
(* On the other hand, we remove at most 4ε good points *)
have Hmax_good_drop : Pr P (good :&: drop) <= 4 * eps.
  by rewrite -Hdrop_ratio; exact/Pr_incl/subsetIr.
pose eps' := Pr P (bad :\: drop) / Pr P (~: drop).
have Hcompl : Pr P (good :\: drop) / Pr P (~: drop) = 1 - eps'.
  apply Rplus_eq_reg_r with (r := eps').
  rewrite -addRA Rplus_opp_l addR0 /eps' /Rdiv -mulRDl.
  apply Rmult_eq_reg_r with (r := Pr P (~: drop)); last by rewrite Pr_of_cplt; lra.
  rewrite mul1R -mulRA Rinv_l ?mulR1; last by rewrite Pr_of_cplt; lra.
  rewrite -Pr_union_disj; first by rewrite -setDUl setUCr setTD.
  by rewrite -setI_eq0 -setDIl setICr set0D.
have Heps'pos : 0 <= eps'.
  by apply: mulR_ge0 => //; apply/ltRW/invR_gt0; rewrite Pr_of_cplt; lra.
have Heps'le1 : eps' <= 1.
  unfold eps'.
  apply Rmult_le_reg_r with (r := Pr P (~: drop)); first by rewrite Pr_of_cplt; lra.
  rewrite mul1R -mulRA Rinv_l ?mulR1; last by rewrite Pr_of_cplt; lra.
  exact/Pr_incl/subsetDr.
(* Remaining good points: 1 - (4 * eps) / (1 - eps) *)
pose delta := 1 - (4 * eps) / (1 - eps).
have Hmin_good_remain : delta <= Pr P (good :\: drop) / Pr P good.
  unfold delta.
  rewrite Pr_diff H.
  apply: (@leR_trans ((1 - eps - 4 * eps) / (1 - eps))).
    apply Rmult_le_reg_r with (r:=1-eps); first lra.
    rewrite -(mulRA _ (/ _)) Rinv_l ?mulR1; last lra.
    by rewrite mulRDl -mulNR -(mulRA _ (/ _)) Rinv_l; lra.
  apply Rmult_le_reg_r with (r:= 1-eps); first lra.
  repeat rewrite (Rmult_assoc _ (/_)).
  by rewrite Rinv_l ?mulR1; lra.
have Hdelta_pos : 0 < delta.
  unfold delta.
  apply Rmult_lt_reg_r with (r := 1-eps); first lra.
  by rewrite mul0R mulRDl mul1R -mulNR -mulRA Rinv_l; lra.
have Hdelta_le1 : delta <= 1.
  unfold delta.
  apply Rmult_le_reg_r with (r:=1-eps); first lra.
  by rewrite mul1R mulRDl mul1R -mulNR -mulRA Rinv_l ?mulR1; lra.
have HEXgood_bound : `| `E_[X | good :\: drop ] - `E_[X | good] | <=
                     sqrt (`V_[X | good] * 2 * (1 - delta) / delta).
  destruct (Req_dec (Pr P (good :\: drop)) (Pr P good)).
  - have -> : `E_[X | (good :\: drop)] = `E_[X | good].
      apply eq_bigr => i _.
      rewrite e.
      apply/Rmult_eq_compat_r/Rmult_eq_compat_l.
      rewrite setIDA.
      rewrite Pr_diff.
      rewrite Pr_diff in e.
      apply/subR_eq; rewrite addRC; apply/subR_eq; rewrite subRR.
      rewrite -setIA.
      apply/eqR_le; split => //.
      have : Pr P (finset (preim X (pred1 i)) :&: (good :&: drop)) <= Pr P (good :&: drop).
        exact/Pr_incl/subsetIr.
      lra.
    unfold Rminus.
    by rewrite Rplus_opp_r Rabs_R0; exact: sqrt_pos.
  - apply resilience'.
    + unfold delta.
      apply Rmult_lt_reg_r with (r := 1 - eps); first lra.
      by rewrite mul0R mulRDl ?mul1R -mulNR -(mulRA _ (/ _)) Rinv_l; lra.
    + lra.
    + suff : Pr P (good :\: drop) <= Pr P good by lra.
      exact/Pr_incl/subsetDl.
    + exact: subsetDl.
have HEXbad_bound :
  0 < Pr P (bad :\: drop) -> `| `E_[ X | bad :\: drop ] - mu | <= sqrt (sigma / eps).
  move=> Pr_bd.
  rewrite -(mulR1 mu) -(Ind_one (bad :\: drop)); last lra.
  rewrite 2!cEx_ExInd.
  rewrite /Rdiv /Rminus.
  rewrite -mulNR.
  rewrite mulRA.
  rewrite -I_double.
  rewrite -mulRDl.
  rewrite big_distrr /=.
  unfold "`E".
  rewrite -big_split.
  have -> :
    \sum_(i in U) (X i * Ind (A:=U) (bad :\: drop) i * P i + - mu * (Ind (A:=U) (bad :\: drop) i * P i)) =
    \sum_(i in U) (X i - mu) * Ind (A:=U) (bad :\: drop) i * P i.
    apply congr_big.
    auto. auto.
    intros.
    lra.
  rewrite normRM.
  rewrite (Rabs_pos_eq (/ _)); last exact/ltRW/invR_gt0.
  apply Rmult_le_reg_r with (r:=Pr P (bad :\: drop)) => //.
  rewrite Rmult_assoc.
  rewrite Rinv_l ?mulR1; last lra.
  apply Rle_trans with (r2 := \sum_(i in U) `|((X i - mu) * Ind (A:=U) (bad :\: drop) i * P i)|).
    exact: leR_sumR_Rabs.
  unfold Pr.
  rewrite big_distrr /=.
  rewrite (bigID (pred_of_set (bad :\: drop))) /=.
  have -> : \sum_(i | ~~ (pred_of_set (bad :\: drop)) i) `|(X i - mu) * Ind (A:=U) (bad :\: drop) i * P i| = 0.
    apply psumR_eq0P.
    - by intros; apply Rabs_pos.
    - intros.
      rewrite -Rabs_R0.
      apply congr1.
      unfold Ind.
      case : ifPn => abd.
        unfold "\in" in abd.
        simpl in abd.
        by rewrite abd in H0.
      simpl in H0.
      inversion H0.
      lra.
  rewrite addR0.
  apply leq_sumR => i H0.
  rewrite normRM (Rabs_pos_eq (P i)) //.
  apply Rmult_le_compat_r => //.
  unfold Ind.
  rewrite H0 mulR1.
  move: H0; rewrite in_setD => /andP [H2 H3].
  destruct (i \in bad) eqn: e1 => //.
  destruct (Rlt_dec (sqrt (sigma / eps)) (`|X i - mu|) ).
    by rewrite Hquantile_drop_bad in H2.
  lra.
have Hmax_bad_remain : Pr P (bad :\: drop) <= eps / Pr P (~: drop).
  rewrite Pr_of_cplt Hdrop_ratio Pr_diff Hbad_ratio.
  apply Rle_trans with (r2 := eps).
    apply Rplus_le_reg_r with (r:=- (eps - Pr P (bad :&: drop))).
    rewrite Rplus_opp_r.
    rewrite Ropp_minus_distr.
    unfold Rminus.
    by rewrite addRCA (addRC eps) Rplus_opp_l addR0.
  apply Rmult_le_reg_r with (r := 1 - 4* eps); first lra.
  by rewrite -(mulRA eps) Rinv_l; nra.
have HEX_not_drop :
  `E_[ X | ~: drop ]  =
    (`E_[ X | good :\: drop ] * Pr P (good :\: drop)
    + `E_[ X | bad :\: drop ] * Pr P (bad :\: drop)) / Pr P (~: drop).
  have H0 : Pr P (good :\: drop) + Pr P (bad :\: drop) = Pr P (~: drop).
    have -> : Pr P (good :\: drop) + Pr P (bad :\: drop) =
      Pr P (good :\: drop) + Pr P (bad :\: drop) - Pr P ((good :\: drop) :&: (bad :\: drop)).
      have -> : (good :\: drop) :&: (bad :\: drop) = set0.
        by rewrite !setDE setIACA setIid setICr set0I.
      by rewrite Pr_set0; lra.
    rewrite -Pr_union_eq.
    suff : good :\: drop :|: bad :\: drop = ~: drop by move=> ->.
    by rewrite -setDUl setUCr setTD.
  have H1 : Pr P (good :\: drop) > 0 by rewrite Pr_diff H; lra.
  destruct (Req_dec (Pr P (bad :\: drop)) 0).
    rewrite e. rewrite Rmult_0_r.
    rewrite addR0.
    rewrite e in H0.
    rewrite addR0 in H0.
    rewrite H0.
    rewrite divRE.
    rewrite Rmult_assoc.
    rewrite Rinv_r.
    rewrite mulR1.
    repeat rewrite cEx_ExInd.
    rewrite H0.
    unfold Rdiv.
    apply/Rmult_eq_compat_r/congr_big.
    auto.
    auto.
    intros.
    unfold ambient_dist.
    repeat rewrite Rmult_assoc.
    apply Rmult_eq_compat_l.
    unfold Ind.
    rewrite in_setD.
    rewrite in_setC.
    unfold "\notin".
    assert (i \in bad :\: drop -> P i = 0).
    apply Pr_set0P.
    auto.
    rewrite in_setD in H3.
    rewrite in_setC in H3.
    move: H3; case: (i \in drop)=> H3.
    simpl.
    auto.
    move: H3; case: (i \in good)=> H3.
    simpl.
    auto.
    simpl.
    rewrite H3.
    lra.
    auto.
    rewrite Pr_of_cplt.
    lra.
  apply (Rmult_eq_reg_r (Pr P (~: drop))).
  repeat rewrite cEx_ExInd.
  repeat rewrite Rmult_assoc.
  repeat rewrite Rinv_l.
  repeat rewrite mulR1.
  unfold "`E".
  rewrite -big_split.
  apply congr_big.
  auto. auto.
  intros.
  simpl.
  unfold ambient_dist, Ind.
  repeat rewrite in_setD.
  rewrite in_setC.
  unfold "\notin".
  destruct (i \in drop).
  simpl. lra.
  simpl.
  unfold bad. rewrite in_setC.
  destruct (i \in good); simpl; nra.
  auto.
  nra.
  rewrite Pr_of_cplt; nra.
  rewrite Pr_of_cplt; nra.
unfold mu_hat.
rewrite HEX_not_drop.
assert (eps' + Pr P (good :\: drop) / Pr P (~: drop) = 1).
nra.
rewrite -(mulR1 mu).
rewrite -H0.
rewrite Rmult_plus_distr_l.
unfold Rdiv at 1.
rewrite mulRDl.
unfold Rminus.
rewrite Ropp_plus_distr.
rewrite Rplus_assoc.
rewrite Rplus_comm.
rewrite -Rplus_assoc.
repeat rewrite -mulNR.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
rewrite -mulRDl.
rewrite Rplus_assoc.
rewrite -mulRDl.
rewrite (Rplus_comm (-mu)).
apply Rle_trans with (r2 :=
  `|(`E_[X | (bad :\: drop)] + - mu) * eps'| +
  `|(`E_[X | (good :\: drop)] + - mu) * (1 - eps')|).
  rewrite -Hcompl.
  by apply Rabs_triang.
rewrite 2!normRM.
rewrite (Rabs_pos_eq (eps')); last lra.
rewrite (Rabs_pos_eq (1 - eps')); last lra.
apply Rle_trans with (r2 :=
  sqrt (`V_[ X | good] / eps) * (eps') +
  sqrt (`V_[ X | good] * 2 * (1 - delta) / delta) * (1 - eps')).
  destruct (Req_dec eps' 0).
    rewrite e.
    by rewrite !(mulR0,add0R,subR0,mulR1).
  destruct (Req_dec eps' 1).
    rewrite e.
    unfold Rminus.
    repeat rewrite Rplus_opp_r.
    repeat rewrite Rmult_0_r.
    repeat rewrite addR0.
    repeat rewrite mulR1.
    apply HEXbad_bound.
    unfold eps' in n.
    rewrite divRE in n.
    apply Rmult_neq_0_reg in n.
    destruct n.
    apply ltR_neqAle.
    split.
    auto.
    by apply Pr_ge0.
  destruct (Req_dec (Pr P (bad :\: drop)) 0).
    assert (eps' = 0) as eps'eq0.
    unfold eps'.
    rewrite e.
    nra.
    rewrite eps'eq0.
    repeat rewrite Rmult_0_r.
    repeat rewrite Rplus_0_l.
    repeat rewrite Rminus_0_r.
    repeat rewrite mulR1.
    exact: HEXgood_bound.
  apply Rplus_le_compat;
    try apply Rmult_le_compat_r;
    try rewrite -Hcompl;
    try unfold eps';
    try apply Rmult_le_pos;
    try (apply Rlt_le; apply Rinv_0_lt_compat; rewrite Pr_of_cplt; nra);
    try apply Pr_ge0.
    exact/HEXbad_bound/Pr_gt0/eqP.
  exact HEXgood_bound.
unfold sigma, Rdiv.
rewrite !sqrt_mult //; last 8 first.
  - by apply: cvariance_nonneg; lra.
  - lra.
  - by apply: mulR_ge0; [apply: cvariance_nonneg; lra|lra].
  - lra.
  - apply: mulR_ge0; [|lra].
    by apply: mulR_ge0; [apply: cvariance_nonneg; lra|lra].
  - by apply/ltRW/invR_gt0; lra.
  - by apply: cvariance_nonneg; lra.
  - by apply/ltRW/invR_gt0; lra.
rewrite (Rmult_comm 8).
repeat rewrite Rmult_assoc.
rewrite -Rmult_plus_distr_l.
apply Rmult_le_compat_l; first exact: sqrt_pos.
repeat rewrite <- Rmult_assoc.
repeat rewrite -sqrt_mult; last first.
  - lra.
  - lra.
  - by apply/ltRW/invR_gt0; lra.
  - by apply: mulR_ge0; lra.
apply Rplus_le_reg_l with (r:=- (sqrt (/ eps) * eps' )).
rewrite addRA Rplus_opp_l add0R addRC -mulRN -mulRDr.
rewrite -(sqrt_Rsqr (1 - eps')); last lra.
rewrite -(sqrt_Rsqr (8 + - eps')); last lra.
rewrite -!sqrt_mult; last 4 first.
  - by apply/ltRW/invR_gt0; lra.
  - exact: Rle_0_sqr.
  - apply/mulR_ge0; [lra|].
    by apply/ltRW/invR_gt0; lra.
  - exact: Rle_0_sqr.
apply/sqrt_le_1_alt/Rmult_le_compat.
- apply: mulR_ge0; [lra|].
  by apply/ltRW/invR_gt0; lra.
- exact: Rle_0_sqr.
- apply Rmult_le_reg_r with (r := delta); first lra.
  rewrite -mulRA Rinv_l ?mulR1; last lra.
  apply Rmult_le_reg_l with (r := eps); first lra.
  rewrite! mulRA Rinv_r ?mul1R; last lra.
  apply Rmult_le_reg_r with (r := 1 + - eps); first lra.
  rewrite mulRDl mul1R -mulNR.
  rewrite -(mulRA _ (/ _)) Rinv_l ?mulR1; last lra.
  rewrite -mulRA mulRDl oppRD oppRK mulRDl -(mulRA _ (/ _)) Rinv_l; [nra|lra].
- by apply/Rsqr_incr_1; lra.
Qed.

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
