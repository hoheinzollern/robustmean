From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg matrix.
From mathcomp Require boolp.
From mathcomp Require Import Rstruct.
Require Import Reals Lra ROrderedType.
From infotheo Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop.
From infotheo Require Import proba fdist.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Local Open Scope proba_scope.
Local Open Scope R_scope.

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

End sets_functions.

Section probability.

Variables (U : finType) (P : fdist U).

Lemma cEx_EXInd (X : {RV P -> R}) F :
  `E_[X | F] = `E (X `* Ind (A:=U) F : {RV P -> R}) / Pr P F.
Proof. 
  unfold Pr. (* need some lemmas to avoid unfolds *)
  unfold cEx.
  rewrite -big_distrl /=.
  congr (_ / _).
  under eq_bigr=> i _.
  - rewrite big_distrr.
    have -> : 
      \sum_(i0 in finset (preim X (pred1 i)) :&: F) (i * P i0) =
      \sum_(i0 in finset (preim X (pred1 i)) :&: F)
       (X i0 * Ind (A:=U) F i0 * P i0).
    + apply congr_big => // i0.
      rewrite in_setI /Ind.
      move/andP => [] /in_preim1 -> ->.
      by rewrite mulR1.
    have H1:
      \sum_(i0 in finset (preim X (pred1 i)) :\: F) X i0 * Ind F i0 * P i0 = 0.
    (* This should be true because all elements of the sum are 0 *)
    + rewrite big1 // => i1.
      rewrite in_setD => /andP [H2 H3].
      by rewrite /Ind (negbTE H2) mulR0 mul0R.
    have :
      \sum_(i0 in finset (preim X (pred1 i))) X i0 * Ind F i0 * P i0 =
      \sum_(i0 in finset (preim X (pred1 i)) :&: F) X i0 * Ind F i0 * P i0 +
      \sum_(i0 in finset (preim X (pred1 i)) :\: F) X i0 * Ind F i0 * P i0
        by apply big_setID.
    rewrite H1 addR0 => <-.
    under eq_bigl do rewrite in_preim1'.
    over.
  by rewrite -sum_parti_finType.
Qed.

Lemma sq_RV_ge0 (X : {RV P -> R}) x : 0 <= (X `^2) x.
Proof. exact: pow2_ge_0. Qed.

Lemma Ex_square_ge0 (X: {RV P -> R}) : 0 <= `E (X `^2).
Proof. apply/Ex_ge0/sq_RV_ge0. Qed.

Lemma Ex_square_expansion
  a b (X Y: {RV P -> R}):
  `E ((a `cst* X `+ b `cst* Y) `^2) =
  a * a * `E (X `^2) + b * b * `E (Y `^2) + 2 * a * b * `E (X `* Y:{RV P -> R}).
Proof.
assert (`E ((a `cst* X `+ b `cst* Y) `^2) = 
`E ((a * a) `cst* (X `^2) `+ (b * b) `cst* (Y `^2) `+ (2 * a * b) `cst* (X `* Y))).
apply eq_bigr.
move => i H.
unfold ambient_dist, "`cst*", "`+", "`^2", "`o", "^".
nra.
repeat rewrite E_add_RV in H.
repeat rewrite E_scalel_RV in H.
auto.
Qed.

Lemma Ex_square_eq0 X:
(forall x, X x = 0 \/ P x = 0) <-> `E (X `^2: {RV P -> R}) = 0.
Proof.
split.
- unfold Ex.
  intros.
  apply psumR_eq0P;
  intros;
  unfold ambient_dist, "`^2", "`o", "^";
  pose proof (H a);
  inversion H1;
  nra.
- intros H.
  assert (( forall x : U, X x = 0 \/ P x = 0) <-> (forall x : U, (X `^2: {RV P -> R}) x = 0 \/ P x = 0)).
  split;
  intros;
  pose proof (H0 x);
  inversion H1;
  unfold "`^2", "`o", "^" in *;
  try nra.
  apply H0.
  assert (forall x : U, x \in U -> (X `^2: {RV P -> R}) x * P x = 0).
  apply psumR_eq0P.
  intros.
  unfold "`^2", "`o", "^".
  rewrite Rmult_1_r.
  rewrite <- (Rmult_0_r 0).
  apply Rmult_le_compat; try nra.
  apply FDist.ge0.
  unfold Ex, ambient_dist in H.
  auto.
  intros.
  pose proof (H1 x).
  rewrite inE in H2.
  apply mulR_eq0.
  auto.
Qed.

Lemma Cauchy_Schwarz_proba
  (X Y: {RV P -> R}): 
    Rsqr (`E (X `* Y: {RV P -> R})) <= `E (X `^2) * `E (Y `^2).
Proof.
  pose a:=sqrt (`E (Y `^2)).
  pose b:=sqrt (`E (X `^2)).
  have H2ab : 2 * a * b * (b * a) = a*a*`E (X `^2) + b*b*`E (Y `^2).
    rewrite -(Rsqr_sqrt (`E (X `^2))); last exact: Ex_square_ge0.
    rewrite -(Rsqr_sqrt (`E (Y `^2))); last exact: Ex_square_ge0. 
    by rewrite -/a -/b /Rsqr; nra.
  have [a0|a0] := Req_dec a 0.
    apply sqrt_eq_0 in a0; last exact: Ex_square_ge0.
    have HY : forall y, Y y = 0 \/ P y = 0 by apply /Ex_square_eq0/a0.
    have -> : `E (X `* Y: {RV P -> R}) = 0.
      apply psumR_eq0P => u uU.
        by case : (HY u) => -> ; rewrite mulR0 ?mul0R; apply leRR.
      by case : (HY u) => -> ; rewrite mulR0 ?mul0R. 
    by rewrite Rsqr_0; apply/mulR_ge0; apply Ex_square_ge0.

  have [b0|b0] := Req_dec b 0.
    apply sqrt_eq_0 in b0; last exact: Ex_square_ge0.
    have HX : (forall x, X x = 0 \/ P x = 0) by apply /Ex_square_eq0/b0.
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
 
  apply neg_pos_Rsqr_le.
    rewrite -/a -/b -(@leR_pmul2r (2 * a * b)); last first.
      by apply mulR_gt0 => //; apply mulR_gt0.
    rewrite -subR_ge0 mulNR subR_opp addRC mulRC H2ab. 
    rewrite (mulRC (`E (X `* Y))) -Ex_square_expansion.
      (* is Ex_square_expansion really a good lemma? *)
    by apply Ex_square_ge0.

  {
    fold a. fold b.
    apply Rmult_le_reg_l with (r:=2 * a * b).
    repeat apply Rmult_lt_0_compat; lra.
    apply Rplus_le_reg_r with (r:=-(2 * a * b * `E (X `* Y:{RV P -> R}))).
    rewrite Rplus_opp_r.
    rewrite H2ab.
    rewrite <- (Rmult_opp_opp b).
    rewrite Ropp_mult_distr_l.
    rewrite Ropp_mult_distr_r.
    rewrite <- Ex_square_expansion.
    apply Ex_square_ge0.
  }
Qed.


Lemma I_square F: Ind F = ((Ind F) `^2 : {RV P -> R}).
Proof.
  apply boolp.funext=> x; unfold Ind.
  by destruct (x \in F) eqn:H0;
  unfold "`^2", "`o";
  destruct (x \in F) eqn:H1; lra.
Qed.

Lemma I_double F: Ind F = ((Ind F) `* (Ind F) : {RV P -> R}).
Proof.
  apply boolp.funext=> x; unfold Ind.
  by case : ifPn => H0;
  unfold "`o";
  destruct (x \in F) eqn:H1; lra.
Qed.

(*
Lemma I_mult_one F : (Ind (A:=U) F : {RV P -> R}) `* 1 = Ind (A:=U) F.
(F: {RV P -> R}): (Ind (A:=U) F: {RV P -> R}) `* 1 = (Ind (A:=U) F : {RV P -> R}). *)

(*variance >= 0*)
Lemma variance_nonneg (X : {RV P -> R}) : 0 <= `V X.
Proof.
  unfold "`V", "`E" at 1. unfold ambient_dist. 
  apply sumR_ge0. intros.
  unfold "`^2", "`o", "^".
  apply mulR_ge0.
  rewrite Rmult_1_r.
  apply Rle_0_sqr. auto. 
Qed.

(*prove A1 and A3 for later use*)
Lemma cEx_var (X : {RV P -> R}) F : 0 < Pr P F  -> 
  `| `E_[ X | F ] - `E X | <= sqrt (`V X / Pr P F ).
Proof.
  intros.
  assert (0 <= / Pr P F) as PrPF_pos.
  apply/Rlt_le/invR_gt0.
  auto.
  assert ( Rabs ( `E_[ X | F ] - `E X )  =  Rabs (`E ((X `-cst `E X) `* Ind F: {RV P -> R})) / Pr P F ).
  { unfold Rdiv.
    rewrite <- (Rabs_pos_eq (/Pr P F)).
    rewrite <- (Rabs_mult).
    apply congr1.
    assert (((X `-cst `E X) `* Ind (A:=U) F) = (X `* Ind (A:=U) F `- `E X `cst* Ind (A:=U) F : {RV P -> R})).
    apply boolp.funext=> u.
    unfold "`-", "`cst*", "`-cst".
    lra.
    rewrite H0.
    rewrite E_sub_RV.
    rewrite Rmult_plus_distr_r.
    rewrite E_scalel_RV.
    rewrite E_Ind.
    rewrite Ropp_mult_distr_l_reverse.
    rewrite Rmult_assoc.
    rewrite Rinv_r.
    rewrite Rmult_1_r.
    apply/Rplus_eq_compat_r/cEx_EXInd.
    lra.
    apply PrPF_pos.
  }
  rewrite H0.
  assert (0 <= (`E ((X `-cst `E X) `^2 `* Ind (A:=U) F: {RV P -> R}) * `E (Ind (A:=U) F:{RV P -> R}))).
  {
    apply mulR_ge0.
    apply Ex_ge0.
    intros.
    apply mulR_ge0.
    apply pow2_ge_0.
    unfold Ind.
    case : ifPn.
    auto.
    auto.
    rewrite E_Ind.
    auto.
  }
  apply leR_trans with (y := sqrt ( mknonnegreal (`E (((X `-cst `E X) `^2) `* Ind (A:=U) F: {RV P -> R}) * `E (Ind (A:=U) F:{RV P -> R})) H1) / Pr P F).
  { unfold Rdiv.  
    apply Rmult_le_compat_r.
    apply PrPF_pos.
    rewrite <- sqrt_Rsqr_abs.
    apply sqrt_le_1_alt.
    simpl.
    assert ( (X `-cst `E X ) `* ((Ind (A:=U) F : {RV P -> R}) )  =
    (X `-cst `E X)  `*  (Ind (A:=U) F : {RV P -> R})  `*  (Ind (A:=U) F : {RV P -> R}) ).
    - apply boolp.funext=> u. unfold "`^2". simpl. unfold "`o".
    unfold Ind.
    simpl. 
    case : ifPn. lra. lra.
    
    rewrite H2. 
    - assert (((X `-cst `E X) `^2) `* Ind (A:=U) F =
    (((X `-cst `E X) `* Ind (A:=U) F) `^2: {RV P -> R})).
    rewrite I_square.
    apply boolp.funext=> u.
    rewrite -> I_square at 1.
    unfold "`^2". simpl. 
    unfold "`o". lra.
    
    - rewrite H3.
    rewrite -> I_square at 1.
    
    apply Cauchy_Schwarz_proba.
  }
  { unfold Rdiv. unfold nonneg. 
    rewrite <- (sqrt_Rsqr (/ Pr P F)).
    rewrite <- sqrt_mult_alt.

    - apply sqrt_le_1_alt.
    unfold "`V".
    rewrite sqrt_Rsqr. unfold Rsqr. rewrite <- Rmult_assoc.
    apply Rmult_le_compat_r.
    apply PrPF_pos.
    rewrite E_Ind. rewrite Rmult_assoc.
    rewrite Rinv_r. rewrite Rmult_1_r.

    - unfold "`E". apply leq_sumR. intros.
    unfold Ind.   
    destruct (i \in F).
    unfold ambient_dist. lra.

    - unfold ambient_dist. apply Rmult_le_compat_r.
    apply FDist.ge0.
    rewrite Rmult_0_r.
    unfold "`^2". unfold "`o".
    apply pow2_ge_0.
    lra.
    apply PrPF_pos.
    apply H1.
    apply PrPF_pos.
  }
Qed.

Lemma cEx_Inv (X: {RV P -> R}) F :
  0 < Pr P F -> Pr P F < 1 ->
  `| `E_[X | F] - `E X| = (1 - Pr P F) / Pr P F * `| `E_[X | (~: F)] - `E X|.
Proof.
  intros.
  
  apply Rmult_eq_reg_l with (r := (Pr P F)).
  - rewrite <- Rmult_assoc.
  rewrite divRE.
  rewrite <- Rmult_assoc.
  rewrite (Rmult_comm (Pr P F) ((1 - Pr P F))).
  rewrite (Rmult_assoc ((1 - Pr P F)) (Pr P F) (/ Pr P F)).
  rewrite -> (Rinv_r (Pr P F)).
   * rewrite Rmult_1_r.
  

  (*If `|`E_[X | F] - `E X| is positive, 
  then `|`E_[X | (~: F)] - `E X| is negative and vice versa*)
  rewrite <- (Rabs_pos_eq (Pr P F)) at 1.
  rewrite <- (Rabs_pos_eq (1 - Pr P F)).
  rewrite <- Rabs_mult. rewrite <- Rabs_mult.
  rewrite <- Rabs_Ropp.
  apply congr1. (*injectivity*)

  (*- (Pr P F * (`E_[X | F] - `E X)) = (1 - Pr P F) * (`E_[X | (~: F)] - `E X)*)
  apply Rmult_eq_reg_r with (r := -1).
  rewrite mulRN1. rewrite mulRN1.
  rewrite Ropp_involutive.

       rewrite Ropp_mult_distr_l.
       rewrite <- Pr_of_cplt.
       rewrite Rmult_minus_distr_l.
       rewrite Rmult_minus_distr_l.
       rewrite (Ropp_mult_distr_l_reverse (Pr P (~: F)) (`E X)).
       rewrite Rmult_comm. 
       rewrite (Rmult_comm (Pr P F ) (`E X ) ).
       
       rewrite -> Pr_of_cplt at 2.
       rewrite Rmult_minus_distr_r.
       rewrite Rmult_1_l.
       rewrite (Rmult_comm (Pr P F) (`E X ) ).
       rewrite Ropp_minus_distr.
       rewrite subRB.
       rewrite Rplus_comm. 
       rewrite <- addR_opp. rewrite <- addR_opp.
       rewrite Ropp_mult_distr_r.
       rewrite <- Rplus_assoc.
       apply Rplus_eq_compat_r.
       
       rewrite mulNR.
       rewrite addR_opp.
       rewrite <- (Rplus_eq_reg_r (Pr P (~: F) * `E_[X | (~: F)])   (`E_[X | F] * Pr P F)  ) .
        *** lra.
        *** rewrite Rplus_assoc.
            rewrite (Rplus_opp_l (Pr P (~: F) * `E_[X | (~: F)]) ).
            rewrite addR0.
            rewrite Rmult_comm.
            repeat rewrite cEx_EXInd.
            repeat
            (rewrite Rmult_comm;
            rewrite Rmult_assoc;
            rewrite Rinv_l;
            try rewrite Rmult_1_r).
            unfold Ex.

            rewrite <- big_split.
            unfold ambient_dist.
            (*Search (\big[_/_]_(_ <- _) _ = \big[_/_]_(_ <- _) _).*)
            apply congr_big.
            auto.
            auto.
            intros.
            (*unfold Radd_comoid.*)
            (*unfold Ind. simpl.*)
            
            rewrite (Rmult_comm (X i) (if i \in F then R1 else R0)).
            rewrite (Rmult_comm (X i) (if i \in ~: F then R1 else R0)).
            rewrite Rmult_assoc.
            rewrite Rmult_assoc. 
            rewrite Rmult_comm.
            rewrite (Rmult_comm (if i \in ~: F then R1 else R0)).
            rewrite <- (Rmult_plus_distr_l (X i * P i)).
            simpl.
            (*apply FDist.f1.*)
            
            (*Search (_ \in ~: _ ).*)
            rewrite in_setC.
            unfold "\notin".

            case : ifPn.
            rewrite addR0. lra.
            lra.
                  + rewrite Pr_of_cplt. lra. 
                  + (*Pr P F <> 0*) lra.

      ** (*-1 <> 0*) lra.
      ** (*0 <= 1 - Pr P F*) lra.
      ** (*0 <= Pr P F*) lra.
    * (*Pr P F <> 0*) lra.
  - (*Pr P F <> 0*) lra.
Qed.

Lemma resilience (delta: R) (X : {RV P -> R}) F:
  0 < delta -> delta <= Pr P F -> Pr P F < 1 ->
    `| `E_[ X | F ] - `E X | <= sqrt (`V X * 2 * (1-delta) / delta).
Proof.
  intros.
  destruct (Rle_or_lt delta (1/2)).
  { (*Pr P F <= 1/2 , A.3 implies the desired result*)
    apply leR_trans with (y := sqrt (`V X / Pr P F )).
    apply cEx_var. lra.
    apply sqrt_le_1_alt. unfold Rdiv.
    repeat rewrite -> Rmult_assoc.
    apply Rmult_le_compat_l.
    apply variance_nonneg. 

    rewrite <- Rmult_1_l at 1.
    rewrite <- Rmult_assoc. 
    apply leR_pmul; try (apply/Rlt_le/invR_gt0); try lra.
    apply leR_inv. assumption. 
    lra.
  }

  { (*Prob > 1/2 and delta < Probability*)
    rewrite cEx_Inv.
    (*Search (?x <= ?y -> ?y <= ?z -> ?x <= ?z).*)
    apply Rle_trans with (r2 := ((1 - Pr P F) / Pr P F * sqrt (`V X / Pr P (~: F)))).
    assert (0 < Pr P F). lra.
    
    apply Rmult_le_compat_l.
    - apply divR_ge0; lra.
    - apply cEx_var; rewrite Pr_of_cplt; lra.
    
    - (*(1 - Pr P F) / Pr P F * sqrt (`V X / Pr P (~: F)) <=
    sqrt (`V X * 2 * (1 - delta) / delta)*) 
    rewrite <- (Rabs_pos_eq ((1 - Pr P F) / Pr P F )).
    rewrite <- sqrt_Rsqr_abs;
    rewrite <- sqrt_mult_alt.
    apply sqrt_le_1_alt;
    (*((1 - Pr P F) / Pr P F)² * (`V X / Pr P (~: F)) <=
`V X * 2 * (1 - delta) / delta*)
    (*Search (?x / ?y = ?x * _).*)
    repeat rewrite divRE;
    rewrite <- Rmult_assoc;
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
    rewrite <- (Rmult_assoc (1 - Pr P F) (/ (1 - Pr P F)));
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
    rewrite Rmult_1_r;
    apply Rmult_le_reg_r with (r := (Pr P F * Pr P F)). nra.
    
    repeat rewrite Rmult_assoc;
    rewrite (Rmult_comm (delta));
    rewrite  (Rmult_assoc (Pr P F));
    rewrite <- (Rmult_assoc (/ Pr P F ) (Pr P F));
    rewrite Rinv_l.
    rewrite Rmult_1_l;
    rewrite <- (Rmult_assoc (/ Pr P F));
    rewrite Rinv_l.
    rewrite Rmult_1_l. 

    (*Search (?x * ?y <= ?z * ?u).*)
    repeat rewrite <- Rmult_assoc;
    apply Rmult_le_compat.

    lra. lra. nra.
    lra. lra. lra. lra. lra.

    - (*0 <= ((1 - Pr P F) / Pr P F)²*)
    apply Rle_0_sqr.
    - apply divR_ge0.   
      * lra. 
      * lra.
    - lra. 
    - lra. 
   (*THE END*)
  }

Qed.

Definition cVar (X : {RV P -> R}) F
  := let miu := `E_[X | F] in `E_[(X `-cst miu) `^2 | F].
Notation "`V_[ X | F ]" := (cVar X F).

Lemma cEx_var' (X : {RV P -> R}) (F G: {set U}) : 0 < Pr P F  -> 
  F \subset G ->
  let mu := `E_[X | G] in
  let var := `V_[X | G] in
  `| `E_[ X | F ] - mu | <= sqrt (var * Pr P G / Pr P F ).
  Proof.
    intros.
    assert (0 <= / Pr P F) as PrPF_pos.
    apply/Rlt_le/invR_gt0.
    auto.
    assert ( `| `E_[ X | F ] - mu |  =  `| `E ((X `-cst mu) `* Ind F: {RV P -> R}) | / Pr P F ).
    { unfold Rdiv.
      rewrite <- (Rabs_pos_eq (/Pr P F)).
      rewrite <- (Rabs_mult).
      apply congr1.
      assert (((X `-cst mu) `* Ind (A:=U) F) = (X `* Ind (A:=U) F `- mu `cst* Ind (A:=U) F : {RV P -> R})).
      apply boolp.funext=> u.
      unfold "`-", "`cst*", "`-cst".
      lra.
      rewrite H1.
      rewrite E_sub_RV.
      rewrite Rmult_plus_distr_r.
      rewrite E_scalel_RV.
      rewrite E_Ind.
      rewrite Ropp_mult_distr_l_reverse.
      rewrite Rmult_assoc.
      rewrite Rinv_r.
      rewrite Rmult_1_r.
      apply/Rplus_eq_compat_r/cEx_EXInd.
      lra.
      apply PrPF_pos.
    }
    rewrite H1.
    assert (0 <= (`E ((X `-cst mu) `^2 `* Ind (A:=U) F: {RV P -> R}) * `E (Ind (A:=U) F:{RV P -> R}))).
    {
      apply mulR_ge0.
      apply Ex_ge0.
      intros.
      apply mulR_ge0.
      apply pow2_ge_0.
      unfold Ind.
      case : ifPn.
      auto.
      auto.
      rewrite E_Ind.
      auto.
    }
    apply leR_trans with (y := sqrt ( mknonnegreal (`E (((X `-cst mu) `^2) `* Ind (A:=U) F: {RV P -> R}) * `E (Ind (A:=U) F:{RV P -> R})) H2) / Pr P F).
    { unfold Rdiv.  
      apply Rmult_le_compat_r.
      apply PrPF_pos.
      rewrite <- sqrt_Rsqr_abs.
      apply sqrt_le_1_alt.
      simpl.
      assert ( (X `-cst mu ) `* ((Ind (A:=U) F : {RV P -> R}) )  =
      (X `-cst mu)  `*  (Ind (A:=U) F : {RV P -> R})  `*  (Ind (A:=U) F : {RV P -> R}) ).
      - apply boolp.funext=> u. unfold "`^2". simpl. unfold "`o".
      unfold Ind.
      simpl. 
      case : ifPn. lra. lra.
      
      rewrite H3.
      - assert (((X `-cst mu) `^2) `* Ind (A:=U) F =
      (((X `-cst mu) `* Ind (A:=U) F) `^2: {RV P -> R})).
      rewrite I_square.
      apply boolp.funext=> u.
      rewrite -> I_square at 1.
      unfold "`^2". simpl. 
      unfold "`o". lra.
      
      - rewrite H4.
      rewrite -> I_square at 1.
      
      apply Cauchy_Schwarz_proba.
    }
    { unfold Rdiv. unfold nonneg. 
      rewrite <- (sqrt_Rsqr (/ Pr P F)).
      rewrite <- sqrt_mult_alt.
  
      - apply sqrt_le_1_alt.
      unfold var, cVar. rewrite cEx_EXInd.
      rewrite sqrt_Rsqr. unfold Rsqr. rewrite <- Rmult_assoc.
      apply Rmult_le_compat_r.
      apply PrPF_pos.
      rewrite E_Ind. repeat rewrite Rmult_assoc.
      rewrite Rinv_r. rewrite Rinv_l. repeat rewrite Rmult_1_r.
  
      - unfold "`E".
      apply leq_sumR.
      intros.
      unfold Ind, ambient_dist, mu.
      case : ifPn => HiF.
      assert (i \in G) as HiG.
      rewrite <- sub1set.
      apply: subset_trans; last exact H0.
      rewrite sub1set.
      auto.

      rewrite HiG.
      nra.
      destruct (i \in G);
      apply Rmult_le_compat_r;
      try apply FDist.ge0;
      apply Rmult_le_compat_l;
      try (unfold "`^2", "`o";
      apply pow2_ge_0);
      try nra.
      assert (Pr P F <= Pr P G).
      apply Pr_incl.
      auto.
      lra.
      lra.
      apply/Rlt_le/Rinv_0_lt_compat.
      lra.
      auto.
      auto.
    }
  Qed. 

Lemma cEx_Inv' (X: {RV P -> R}) (F G : {set U}) :
  0 < Pr P F -> F \subset G -> Pr P F < Pr P G ->
  `| `E_[X | F] - `E_[X | G]| = (Pr P (G :\: F)) / (Pr P F) * `| `E_[X | (G :\: F)] - `E_[X | G]|.
Proof.
  intros.

  assert (G :&: F = F).
  {
    apply: setIidPr.
    auto.
  }
  apply Rmult_eq_reg_l with (r:=Pr P F).
  unfold Rdiv.
  rewrite (Rmult_comm (Pr P (G :\: F))).
  repeat rewrite <- Rmult_assoc.
  rewrite Rinv_r.
  rewrite Rmult_1_l.
  rewrite <- (Rabs_pos_eq (Pr _ F)).
  rewrite <- (Rabs_pos_eq (Pr _ (G :\: F))).
  repeat rewrite <- Rabs_mult.
  rewrite Rmult_comm.
  rewrite (Rmult_comm (Pr P (G :\: F))).
  repeat rewrite cEx_EXInd.
  unfold Rminus.
  repeat rewrite Rmult_plus_distr_r.
  repeat rewrite Rmult_assoc.
  repeat rewrite Rinv_l.
  repeat rewrite Rmult_1_r.
  rewrite <- Rabs_Ropp.
  apply congr1.
  apply Rplus_eq_reg_r with (r := 
  (`E (X `* Ind (A:=U) F : {RV P -> R}) + - (`E (X `* Ind (A:=U) G : {RV P -> R}) / Pr P G) * Pr P F)).
  rewrite Rplus_opp_l.
  repeat rewrite <- Rplus_assoc.
  rewrite Ropp_mult_distr_l.
  assert (
    `E (X `* Ind (A:=U) (G :\: F) : {RV P -> R}) +
    - `E (X `* Ind (A:=U) G : {RV P -> R}) * / Pr P G * Pr P (G :\: F) + 
    `E (X `* Ind (A:=U) F : {RV P -> R}) + - `E (X `* Ind (A:=U) G : {RV P -> R}) * / Pr P G * Pr P F =
    `E (X `* Ind (A:=U) (G :\: F) : {RV P -> R}) + `E (X `* Ind (A:=U) F : {RV P -> R}) +
    - `E (X `* Ind (A:=U) G : {RV P -> R}) * / Pr P G * (Pr P (G :\: F) + Pr P F)
  ).
  lra.
  rewrite H3.
  rewrite Pr_diff.
  rewrite H2.
  unfold Ex at 1.
  unfold Ex at 1.
  unfold ambient_dist.
  rewrite <- big_split.
  simpl.
  rewrite Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite addR0.
  rewrite Rmult_assoc.
  rewrite Rinv_l.
  rewrite Rmult_1_r.
  apply Rplus_eq_reg_r with (r:= `E (X `* Ind (A:=U) G: {RV P -> R})).
  rewrite Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite addR0.
  rewrite Rplus_0_l.
  unfold Ex.
  unfold ambient_dist.
  apply congr_big.
  auto.
  auto.
  intros.
  rewrite <- Rmult_plus_distr_r.
  apply Rmult_eq_compat_r.
  rewrite <- Rmult_plus_distr_l.
  unfold Ind.
  rewrite in_setD.
  unfold "\notin".
  destruct (i \in F) eqn:HiF.
  assert (i \in G) as HiG.
  rewrite <- sub1set.
  apply: subset_trans; last exact H0.
  rewrite sub1set.
  auto.
  rewrite HiG.
  simpl.
  lra.
  simpl.
  lra.
  assert (Pr P F <= Pr P G).
  apply Pr_incl. auto.
  all: try rewrite Pr_diff.
  all: try rewrite H2.
  all: try lra.
Qed.

Lemma cvariance_nonneg (X : {RV P -> R}) F : 0 < Pr P F -> 0 <= `V_[X | F].
(* note: we could drop 0 < Pr P F *)
Proof.
  intros.
  unfold cVar.
  rewrite cEx_EXInd.
  unfold Ex.
  unfold ambient_dist.
  unfold Rdiv.
  rewrite big_distrl. simpl. 
  apply sumR_ge0. intros.
  unfold "`^2", "`o", "^".
  apply mulR_ge0.
  rewrite Rmult_1_r.
  apply mulR_ge0.
  apply mulR_ge0.
  apply Rle_0_sqr.
  unfold Ind.
  destruct (i \in F) eqn:H1;
  rewrite H1; lra.
  apply FDist.ge0.
  apply/Rlt_le/Rinv_0_lt_compat.
  auto.
Qed.

Lemma resilience' (delta: R) (X : {RV P -> R}) (F G: {set U}):
  0 < delta -> delta <= Pr P F / Pr P G -> Pr P F < Pr P G -> F \subset G ->
    `| `E_[ X | F ] - `E_[ X | G ] | <= sqrt (`V_[ X | G ] * 2 * (1-delta) / delta).
Proof.
    intros.
    assert (0 < Pr P G) as HPrGpos.
    {
      apply Rle_lt_trans with (r2 := Pr P F).
      apply Pr_ge0.
      auto.
    }
    assert (0 < Pr P F) as HPrFpos.
    {
      apply Rlt_le_trans with (r2 := delta * Pr P G).
      apply Rmult_lt_0_compat; lra.
      apply Rmult_le_reg_r with (r := / Pr P G).
      apply Rinv_0_lt_compat; auto.
      rewrite Rmult_assoc.
      rewrite Rinv_r.
      rewrite Rmult_1_r.
      auto.
      lra.
    }
    assert (G :&: F = F) as HGnF_F.
    {
      apply: setIidPr.
      auto.
    }
    assert (delta < 1) as Hdelta_pos.
    {
      apply Rmult_le_compat_r with (r:= Pr P G) in H0.
      rewrite Rmult_assoc in H0.
      rewrite Rinv_l in H0.
      rewrite Rmult_1_r in H0.
      all: nra.
    }
    destruct (Rle_or_lt delta (1/2)).
    { (*Pr P F <= 1/2 , A.3 implies the desired result*)
      apply leR_trans with (y := sqrt (`V_[X | G] * Pr P G / Pr P F )).
      apply cEx_var'. nra. auto.
      apply sqrt_le_1_alt. unfold Rdiv.
      repeat rewrite -> Rmult_assoc.
      apply Rmult_le_compat_l.
      apply cvariance_nonneg. auto.
      apply Rle_trans with (r2 := 1/delta).
      apply Rmult_le_reg_r with (r := delta * Pr P F / Pr P G).
      nra.
      unfold Rdiv.
      repeat rewrite <- (Rmult_assoc).
      assert (Pr P G * / Pr P F * delta * Pr P F * / Pr P G =
      delta * (Pr P G * / Pr P G) * (Pr P F * / Pr P F)).
      lra.
      rewrite H4.
      repeat rewrite Rinv_r; repeat rewrite Rmult_1_r.
      rewrite Rmult_1_l.
      rewrite Rinv_l.
      rewrite Rmult_1_l.
      all: try lra.
      apply Rmult_le_reg_r with (r:= delta).
      lra.
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
      - apply cEx_var'. rewrite Pr_diff. rewrite HGnF_F. lra. apply subsetDl.
      
      apply Rle_trans with (r2 := sqrt (`V_[ X | G] * (Pr P G * (1 - delta)) / (Pr P G * delta * delta))).

      rewrite <- (Rabs_pos_eq (Pr P (G :\: F) / Pr P F)).
      rewrite <- sqrt_Rsqr_abs;
      rewrite <- sqrt_mult_alt.
      apply sqrt_le_1_alt.
      unfold Rdiv.
      repeat rewrite <- Rmult_assoc.
      rewrite (Rmult_comm _  (`V_[X | G])).
      repeat rewrite Rmult_assoc;
      apply Rmult_le_compat_l. 
  
      apply cvariance_nonneg. auto.

      repeat rewrite <- Rmult_assoc.
      rewrite Rmult_comm.
      repeat rewrite <- Rmult_assoc.
      rewrite Rinv_l.
      rewrite Rmult_1_l.
      rewrite Rmult_comm.
      rewrite (Rmult_comm (/Pr P F)).
      rewrite Rmult_assoc.
      rewrite <- Rinv_mult_distr.
      rewrite <- Rmult_assoc.
      apply Rmult_le_reg_r with (r:=Pr P F * Pr P F).
      nra.
      rewrite Rmult_assoc.
      rewrite Rinv_l.
      rewrite Rmult_1_r.
      rewrite Rmult_assoc.
      rewrite (Rmult_comm (/ _)).
      rewrite <-Rmult_assoc.
      apply Rmult_le_reg_r with (r:= Pr P G * delta * delta).
      apply Rmult_lt_0_compat.
      nra. lra.
      rewrite (Rmult_assoc _ (/ _)).
      rewrite Rinv_l.
      rewrite Rmult_1_r.
      apply Rmult_le_compat_r with (r:= Pr P G) in H0.
      rewrite Rmult_assoc in H0.
      rewrite Rinv_l in H0.
      rewrite Rmult_1_r in H0.
      rewrite (Rmult_comm (Pr P G)).
      rewrite Rmult_assoc.
      apply Rmult_le_compat.
      apply Pr_ge0.
      nra.
      rewrite Pr_diff.
      rewrite HGnF_F.
      apply Rle_trans with (r2:=Pr P G - delta * Pr P G).
      nra.
      nra.
      rewrite Rmult_comm.
      rewrite Rmult_assoc.
      rewrite (Rmult_comm (delta)).
      apply Rmult_le_compat.
      all: try nra.
      repeat apply Rmult_integral_contrapositive_currified; nra.
      rewrite Pr_diff. rewrite HGnF_F. nra.
      apply Rle_0_sqr.
      rewrite Pr_diff.
      rewrite HGnF_F.
      apply/Rlt_le/Rmult_lt_0_compat.
      nra.
      apply Rinv_0_lt_compat.
      nra.
      apply sqrt_le_1_alt.
      unfold Rdiv.
      rewrite Rinv_mult_distr.
      rewrite <- Rmult_assoc.
      apply Rmult_le_compat_r.
      apply/Rlt_le/Rinv_0_lt_compat.
      lra.
      repeat rewrite Rmult_assoc.
      apply Rmult_le_compat_l.
      apply cvariance_nonneg.
      lra.
      rewrite Rinv_mult_distr.
      rewrite <- Rmult_assoc.
      rewrite (Rmult_comm (Pr P G)).
      rewrite <- Rmult_assoc.
      rewrite (Rmult_assoc (1 - delta)).
      rewrite Rinv_r.
      rewrite Rmult_1_r.
      rewrite (Rmult_comm 2).
      repeat rewrite Rmult_assoc.
      apply Rmult_le_compat_l.
      all: try nra.
      apply Rmult_le_reg_r with (r:=delta).
      lra.
      rewrite Rinv_l.
      lra.
      nra.
      auto.
  }
  Qed.

Infix ">=?" := Rgeb : R_scope.

Lemma Ind_one F :
  Pr P F <> 0 -> `E_[Ind F : {RV P -> R} | F] = 1.
Proof.
  intros.
  rewrite cEx_EXInd.
  assert (Ind F `* Ind F = Ind F) as I_mult.
  {
    apply boolp.funext=> u.
    unfold Ind.
    case : ifPn; nra.
  }
  rewrite I_mult.
  rewrite E_Ind.
  unfold Rdiv.
  rewrite Rinv_r.
  lra.
  lra.
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
  intros bad mu_hat mu sigma
    Hmin_outliers Hmax_outliers Hbad_ratio Hdrop_ratio Hquantile_drop_bad.
  assert (Pr P good = 1 - eps).
  {
    rewrite <- Ropp_involutive.
    rewrite <- Ropp_involutive at 1.
    apply/Ropp_eq_compat/(Rplus_eq_reg_l 1).
    assert (1 + - Pr P good = 1 - Pr P good).
    auto.
    rewrite H.
    rewrite <- Pr_of_cplt.
    rewrite Hbad_ratio. nra.
  }
  (* On the other hand, we remove at most 4ε good points *)
  assert (Pr P (good :&: drop) <= 4 * eps) as Hmax_good_drop.
  {
    rewrite <- Hdrop_ratio.
    apply Pr_incl.
    apply subsetIr.
  }
  pose (eps' := Pr P (bad :\: drop) / Pr P (~: drop)).
  assert (Pr P (good :\: drop) / Pr P (~: drop) = 1 - eps') as Hcompl.
  {
    apply Rplus_eq_reg_r with (r := eps').
    unfold Rminus.
    rewrite Rplus_assoc.
    rewrite Rplus_opp_l.
    rewrite addR0.
    unfold eps', Rdiv.
    rewrite <- Rmult_plus_distr_r.
    apply Rmult_eq_reg_r with (r:=Pr P (~: drop)).
    rewrite Rmult_assoc.
    rewrite Rinv_l.
    rewrite Rmult_1_l.
    rewrite Rmult_1_r.
    rewrite <- Pr_union_disj.
    apply congr1.
    rewrite <- setDUl.
    rewrite setUCr.
    rewrite setTD.
    auto.
    rewrite <- setI_eq0.
    rewrite <- setDIl.
    rewrite setICr.
    rewrite set0D.
    auto.
    all: rewrite Pr_of_cplt; lra.
  }
  assert (0 <= eps') as Heps'pos.
  {
    unfold eps'.
    rewrite <- (Rmult_0_l 0).
    apply Rmult_le_compat.
    lra. lra.
    apply Pr_ge0.
    apply Rlt_le.
    apply Rinv_0_lt_compat.
    rewrite Pr_of_cplt.
    lra.
  }
  assert (eps' <= 1) as Heps'le1.
  {
    unfold eps'.
    apply Rmult_le_reg_r with (r:=Pr P (~: drop)).
    rewrite Pr_of_cplt.
    lra.
    rewrite Rmult_assoc.
    rewrite Rinv_l.
    rewrite Rmult_1_l.
    rewrite Rmult_1_r.
    apply Pr_incl.
    apply subsetDr.
    rewrite Pr_of_cplt.
    lra.
  }
  (* Remaining good points: 1 - (4 * eps) / (1 - eps) *)
  pose (delta := 1 - (4 * eps) / (1 - eps)).
  assert (delta <= Pr P (good :\: drop) / Pr P good) as Hmin_good_remain.
  {
    unfold delta.
    rewrite Pr_diff.
    rewrite H.
    apply Rle_trans with (r2:=(1 - eps - 4*eps) / (1 - eps)).
    apply Rmult_le_reg_r with (r:=1-eps).
    lra.
    rewrite (Rmult_assoc _ (/ _)).
    rewrite Rinv_l.
    rewrite Rmult_1_r.
    rewrite Rmult_plus_distr_r.
    rewrite Ropp_mult_distr_l.
    rewrite (Rmult_assoc _ (/ _)).
    rewrite Rinv_l.
    lra.
    lra.
    lra.
    apply Rmult_le_reg_r with (r:= 1-eps).
    lra.
    repeat rewrite (Rmult_assoc _ (/_)).
    rewrite Rinv_l.
    repeat rewrite Rmult_1_r.
    lra.
    lra.
  }
  assert (0 < delta) as Hdelta_pos.
  {
    unfold delta.
    apply Rmult_lt_reg_r with (r:=1-eps).
    lra.
    rewrite Rmult_0_l.
    rewrite Rmult_plus_distr_r.
    rewrite Rmult_1_l.
    rewrite Ropp_mult_distr_l.
    rewrite (Rmult_assoc _ (/ _)).
    rewrite Rinv_l.
    lra.
    lra.
  }
  assert (delta <= 1) as Hdelta_le1.
  {
    unfold delta.
    apply Rmult_le_reg_r with (r:=1-eps).
    lra.
    rewrite Rmult_1_l.
    rewrite Rmult_plus_distr_r.
    rewrite Rmult_1_l.
    rewrite Ropp_mult_distr_l.
    rewrite (Rmult_assoc _ (/ _)).
    rewrite Rinv_l.
    rewrite Rmult_1_r.
    lra.
    lra.
  }
  assert (
    `| `E_[X | good :\: drop ] - `E_[X | good] | <= sqrt (`V_[X | good] * 2 * (1 - delta) / delta)
  ) as HEXgood_bound.
  {
    destruct (Req_dec (Pr P (good :\: drop)) (Pr P good)).
    {
      assert (`E_[X | (good :\: drop)] = `E_[X | good]).
      apply eq_bigr.
      intros.
      rewrite e.
      apply Rmult_eq_compat_r.
      apply Rmult_eq_compat_l.
      rewrite setIDA.
      rewrite Pr_diff.
      rewrite Pr_diff in e.
      assert (Pr P (good :&: drop) = 0).
      lra.
      assert (Pr P (finset (preim X (pred1 i)) :&: good :&: drop) = 0).
      rewrite <- setIA.
      assert (Pr P (finset (preim X (pred1 i)) :&: (good :&: drop)) <= Pr P ((good :&: drop)) ).
      apply Pr_incl.
      apply subsetIr.
      rewrite H1 in H2.
      destruct (Pr_ge0 P (finset (preim X (pred1 i)) :&: (good :&: drop))).
      lra.
      lra.
      lra.
      rewrite H0.
      unfold Rminus.
      rewrite Rplus_opp_r.
      rewrite Rabs_R0.
      apply sqrt_pos.
    }
    apply resilience'.
    unfold delta.
    apply Rmult_lt_reg_r with (r:=1-eps).
    lra.
    rewrite Rmult_0_l.
    rewrite Rmult_plus_distr_r.
    rewrite Ropp_mult_distr_l.
    rewrite (Rmult_assoc _ (/ _)).
    rewrite Rinv_l.
    lra.
    lra.
    auto.
    assert (Pr P (good :\: drop) <= Pr P good).
    apply Pr_incl.
    apply subsetDl.
    lra.
    apply subsetDl.
  }
  assert (
    0 < Pr P (bad :\: drop) -> `| `E_[ X | bad :\: drop ] - mu | <= sqrt (sigma / eps)
  ) as HEXbad_bound.
  {
    intros Pr_bd.
    rewrite <- (Rmult_1_r mu).
    rewrite <- (Ind_one (bad :\: drop)).
    rewrite cEx_EXInd.
    rewrite cEx_EXInd.
    unfold Rdiv.
    unfold Rminus.
    rewrite Ropp_mult_distr_l.
    rewrite <- Rmult_assoc.
    rewrite <- I_double.
    rewrite <- Rmult_plus_distr_r.
    rewrite big_distrr.
    simpl.
    unfold "`E".
    rewrite <- big_split.
    assert (
    \sum_(i in U) (X i * Ind (A:=U) (bad :\: drop) i * P i + - mu * (Ind (A:=U) (bad :\: drop) i * P i)) =
    \sum_(i in U) (X i - mu) * Ind (A:=U) (bad :\: drop) i * P i
    ).
    apply congr_big.
    auto. auto.
    intros.
    lra.
    rewrite H0.
    rewrite Rabs_mult.
    rewrite (Rabs_pos_eq (/ _)).
    apply Rmult_le_reg_r with (r:=Pr P (bad :\: drop)).
    auto.
    rewrite Rmult_assoc.
    rewrite Rinv_l.
    rewrite Rmult_1_r.
    apply Rle_trans with (r2 := \sum_(i in U) `|((X i - mu) * Ind (A:=U) (bad :\: drop) i * P i)|).
    apply leR_sumR_Rabs.
    unfold Pr.
    rewrite big_distrr.
    simpl.
    rewrite (bigID (pred_of_set (bad :\: drop))).
    simpl.
    assert (\sum_(i | ~~ (pred_of_set (bad :\: drop)) i) `|(X i - mu) * Ind (A:=U) (bad :\: drop) i * P i| = 0).
    apply psumR_eq0P.
    intros.
    apply Rabs_pos.
    intros.
    rewrite <- Rabs_R0.
    apply congr1.
    unfold Ind.
    case : ifPn => abd.
    unfold "\in" in abd.
    simpl in abd.
    rewrite abd in H1.
    simpl in H1.
    inversion H1.
    lra.
    rewrite H1.
    rewrite addR0.
    apply leq_sumR.
    intros.
    rewrite Rabs_mult.
    rewrite (Rabs_pos_eq (P i)).
    apply Rmult_le_compat_r.
    apply FDist.ge0.
    unfold Ind.
    rewrite H2.
    rewrite Rmult_1_r.
    rewrite in_setD in H2.
    move: H2 => /andP [H2 H3].
    unfold "\notin" in H2.
    destruct (i \in bad) eqn: e1.
    destruct (Rlt_dec (sqrt (sigma / eps)) (`|X i - mu|) ).
    rewrite Hquantile_drop_bad in H2.
    inversion H2. auto. auto.
    lra.
    rewrite Hquantile_drop_bad in H2.
    inversion H2. inversion H3. inversion H3.
    apply FDist.ge0.
    lra.
    apply Rlt_le.
    apply Rinv_0_lt_compat.
    lra.
    lra.
  }
  assert (
    Pr P (bad :\: drop) <= eps / Pr P (~: drop)
  ) as Hmax_bad_remain.
  {
    rewrite Pr_of_cplt.
    rewrite Hdrop_ratio.
    rewrite Pr_diff.
    rewrite Hbad_ratio.
    apply Rle_trans with (r2:=eps).
    apply Rplus_le_reg_r with (r:=- (eps - Pr P (bad :&: drop))).
    rewrite Rplus_opp_r.
    rewrite Ropp_minus_distr.
    unfold Rminus.
    rewrite <- Rplus_assoc.
    rewrite Rplus_comm.
    rewrite <- Rplus_assoc.
    rewrite Rplus_opp_l.
    rewrite Rplus_0_l.
    apply Pr_ge0.
    unfold bad.
    apply Rmult_le_reg_r with (r:=1 - 4* eps).
    lra.
    rewrite (Rmult_assoc eps).
    rewrite Rinv_l.
    nra.
    nra.
  }
  assert (
    `E_[ X | ~: drop ]  =
      (`E_[ X | good :\: drop ] * Pr P (good :\: drop) 
      + `E_[ X | bad :\: drop ] * Pr P (bad :\: drop)) / Pr P (~: drop)
  ) as HEX_not_drop.
  {
    assert (Pr P (good :\: drop) + Pr P (bad :\: drop) = Pr P (~: drop)).
    {
      assert ((good :\: drop) :&: (bad :\: drop) = set0).
      repeat rewrite setDE.
      rewrite setIACA.
      rewrite setIid.
      rewrite setICr.
      rewrite set0I.
      auto.
      assert (
        Pr P (good :\: drop) + Pr P (bad :\: drop) =
        Pr P (good :\: drop) + Pr P (bad :\: drop) - Pr P ((good :\: drop) :&: (bad :\: drop))
      ).
      rewrite H0.
      rewrite Pr_set0.
      lra.
      rewrite H1.
      rewrite <- Pr_union_eq.
      assert (good :\: drop :|: bad :\: drop = ~: drop).
      rewrite <- setDUl.
      rewrite setUCr.
      rewrite setTD.
      auto.
      rewrite H2.
      auto.
    }
    assert (Pr P (good :\: drop) > 0).
    rewrite Pr_diff.
    rewrite H.
    lra.
    destruct (Req_dec (Pr P (bad :\: drop)) 0).
    {
      rewrite e. rewrite Rmult_0_r.
      rewrite addR0.
      rewrite e in H0.
      rewrite addR0 in H0.
      rewrite H0.
      unfold Rdiv.
      rewrite Rmult_assoc.
      rewrite Rinv_r.
      rewrite Rmult_1_r.
      repeat rewrite cEx_EXInd.
      rewrite H0.
      unfold Rdiv.
      apply Rmult_eq_compat_r.
      apply congr_big.
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
    }
    apply (Rmult_eq_reg_r (Pr P (~: drop))).
    repeat rewrite cEx_EXInd.
    repeat rewrite Rmult_assoc.
    repeat rewrite Rinv_l.
    repeat rewrite Rmult_1_r.
    unfold "`E".
    rewrite <- big_split.
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
    all: rewrite Pr_of_cplt; nra.
  }
  unfold mu_hat.
  rewrite HEX_not_drop.
  assert (eps' + Pr P (good :\: drop) / Pr P (~: drop) = 1).
  nra.
  rewrite <- (Rmult_1_r mu).
  rewrite <- H0.
  rewrite Rmult_plus_distr_l.
  unfold Rdiv at 1.
  rewrite Rmult_plus_distr_r.
  unfold Rminus.
  rewrite Ropp_plus_distr.
  rewrite Rplus_assoc.
  rewrite Rplus_comm.
  rewrite <- Rplus_assoc.
  repeat rewrite Ropp_mult_distr_l.
  rewrite Rmult_assoc.
  rewrite Rmult_assoc.
  rewrite <- Rmult_plus_distr_r.
  rewrite Rplus_assoc.
  rewrite <- Rmult_plus_distr_r.
  rewrite (Rplus_comm (-mu)).
  apply Rle_trans with (r2 := 
  `|(`E_[X | (bad :\: drop)] + - mu) * eps'| +
  `|(`E_[X | (good :\: drop)] + - mu) * (1 - eps')|
  ).
  rewrite <- Hcompl.
  apply Rabs_triang.
  rewrite Rabs_mult.
  rewrite Rabs_mult.
  rewrite (Rabs_pos_eq (eps')).
  rewrite (Rabs_pos_eq (1 - eps')).
  apply Rle_trans with (r2 :=
  sqrt (`V_[ X | good] / eps) * (eps') +
  sqrt (`V_[ X | good] * 2 * (1 - delta) / delta) * (1 - eps')
  ).
  destruct (Req_dec eps' 0).
  {
    rewrite e.
    repeat rewrite Rmult_0_r.
    repeat rewrite Rplus_0_l.
    repeat rewrite Rminus_0_r.
    repeat rewrite Rmult_1_r.
    auto.
  }
  destruct (Req_dec eps' 1).
  {
    rewrite e.
    unfold Rminus.
    repeat rewrite Rplus_opp_r.
    repeat rewrite Rmult_0_r.
    repeat rewrite addR0.
    repeat rewrite Rmult_1_r.
    apply HEXbad_bound.
    unfold eps' in n.
    unfold Rdiv in n.
    apply Rmult_neq_0_reg in n.
    destruct n.
    apply ltR_neqAle.
    split.
    auto.
    apply Pr_ge0.
  }
  destruct (Req_dec (Pr P (bad :\: drop)) 0).
  {
    assert (eps' = 0) as eps'eq0.
    unfold eps'.
    rewrite e.
    nra.
    rewrite eps'eq0.
    repeat rewrite Rmult_0_r.
    repeat rewrite Rplus_0_l.
    repeat rewrite Rminus_0_r.
    repeat rewrite Rmult_1_r.
    apply HEXgood_bound.
  }
  apply Rplus_le_compat;
  try apply Rmult_le_compat_r;
  try rewrite <- Hcompl;
  try unfold eps';
  try apply Rmult_le_pos;
  try (apply Rlt_le; apply Rinv_0_lt_compat; rewrite Pr_of_cplt; nra);
  try apply Pr_ge0.
  apply HEXbad_bound.
  apply ROrder.le_neq_lt.
  apply Pr_ge0.
  auto.
  apply HEXgood_bound.
  unfold sigma, Rdiv.
  repeat rewrite -> sqrt_mult.
  rewrite (Rmult_comm 8).
  repeat rewrite Rmult_assoc.
  rewrite <- Rmult_plus_distr_l.
  apply Rmult_le_compat_l.
  apply sqrt_pos.
  repeat rewrite <- Rmult_assoc.
  repeat rewrite <- sqrt_mult.
  apply Rplus_le_reg_l with (r:=- (sqrt (/ eps) * eps' )).
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  rewrite Rplus_comm.
  rewrite Ropp_mult_distr_r.
  rewrite <- Rmult_plus_distr_l.
  rewrite <- (sqrt_Rsqr (1-eps')).
  rewrite <- (sqrt_Rsqr (8+-eps')).
  repeat rewrite <- sqrt_mult.
  apply sqrt_le_1_alt.
  apply Rmult_le_compat.
  apply Rmult_le_reg_r with (r:=delta).
  lra.
  rewrite Rmult_assoc.
  rewrite Rinv_l.
  rewrite Rmult_0_l.
  all: repeat apply Rmult_le_pos.
  all: try apply Rsqr_incr_1.
  all: try (apply Rlt_le; apply Rinv_0_lt_compat).
  all: try apply cvariance_nonneg.
  all: try nra.
  apply Rmult_le_reg_r with (r:=delta).
  lra.
  rewrite Rmult_assoc.
  rewrite Rinv_l.
  rewrite Rmult_1_r.
  apply Rmult_le_reg_l with (r:=eps).
  lra.
  repeat rewrite <- Rmult_assoc.
  rewrite Rinv_r.
  rewrite Rmult_1_l.
  unfold delta, Rminus.
  apply Rmult_le_reg_r with (r:=1+-eps).
  lra.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l.
  rewrite Ropp_mult_distr_l.
  rewrite (Rmult_assoc _ (/ _)).
  rewrite Rinv_l.
  rewrite Rmult_1_r.
  rewrite Rmult_assoc.
  rewrite Rmult_plus_distr_r.
  rewrite Ropp_plus_distr.
  rewrite <- Ropp_mult_distr_l.
  rewrite Ropp_involutive.
  rewrite Rmult_plus_distr_r.
  rewrite (Rmult_assoc _ (/ _)).
  rewrite Rinv_l.
  all: try nra.
  apply Pr_ge0.
  rewrite Pr_of_cplt.
  lra.
Qed.

End probability.

Require Import List.
Require Import Sorting.
Require Import Orders.

Definition Average l := fold_left Rplus l 0 / INR (length l).

Module ROrder <: TotalLeBool.
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
