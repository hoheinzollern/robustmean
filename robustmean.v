From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg matrix.
From mathcomp Require boolp.
From mathcomp Require Import Rstruct.
Require Import Reals Lra Nsatz Psatz ROrderedType.
Require Import Coq.Logic.FunctionalExtensionality.
From infotheo Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop.
From infotheo Require Import proba fdist.
Require Import Setoid Ring.


Local Open Scope proba_scope.
Local Open Scope big_scope.
Local Open Scope R_scope.


Notation "X `* Y" := (fun x => X x * Y x) : proba_scope.


Section sets_functions.

Lemma set1U (X:finType) (A:{set X}) (x:X) : [set x] :&: A = if x \in A then [set x] else set0.
Proof.
  destruct (x \in A) eqn:H0.
  - by apply /setIidPl; rewrite sub1set.
  - by apply /disjoint_setI0; rewrite disjoints1; rewrite H0.
Qed.

Lemma in_preim : forall (A:finType) (B:eqType) (a:A) (b:B) X,
  (a \in finset (T:=A) (preim X (pred1 b))) -> X a = b.
Proof.
  move => A B i i0 X; rewrite in_set; move => /eqP-H; by [].
Qed.

Lemma leq_sumR I r (P : pred I) (E1 E2 : I -> R) :
    (forall i, P i -> E1 i <= E2 i) ->
  \sum_(i <- r | P i) E1 i <= \sum_(i <- r | P i) E2 i.
Proof. move=> leE12. elim/big_ind2: _ => // m1 m2 n1 n2. lra. Qed.

End sets_functions.

Section probability.

Variables (U : finType) (P : fdist U).

Lemma cEx_EXInd (X : {RV P -> R}) F: `E_[X | F] = `E (X `* Ind (A:=U) F : {RV P -> R}) / Pr P F.
Proof. 
  unfold Pr.
  unfold cEx.
  unfold Ex.
  unfold ambient_dist.
  unfold Rdiv.
  rewrite <- big_distrl.
  apply Rmult_eq_compat_r.
  simpl.
  assert (
    \sum_(i <- fin_img (A:=U) (B:=R_eqType) X)
      (i * Pr P (finset (T:=U) (preim X (pred1 i)) :&: F)) =
    \sum_(i <- fin_img (A:=U) (B:=R_eqType) X)
      \sum_(a in U | X a == i) (X a * Ind (A:=U) F a * P a)
  ).
  apply eq_bigr.
  intros.
  unfold Pr.
  rewrite big_distrr.
  simpl.
  assert (
    \sum_(i0 in finset (T:=U) (preim X (pred1 i)) :&: F) (i * P i0) =
    \sum_(i0 in finset (T:=U) (preim X (pred1 i)) :&: F) (X i0 * Ind (A:=U) F i0 * P i0)
  ).
  apply congr_big. auto. auto.
  intros.
  destruct H0.
  rewrite in_setI in H.
  apply andb_true_iff in H.
  destruct H.
  simpl in *.
  assert (X i0 = i).
  apply in_preim. auto.
  rewrite H1.
  unfold Ind.
  destruct (i0 \in F).
  lra.
  inversion H0.
  rewrite H0.
  assert (
    \sum_(i0 in finset (T:=U) (preim X (pred1 i)) :\: F) X i0 * Ind (A:=U) F i0 * P i0 = 0
  ). (* This should be true because all elements of the sum are 0 *)
  apply psumR_eq0P;
  (intros;
  rewrite in_setD in H1;
  apply andb_true_iff in H1;
  destruct H1;
  unfold Ind;
  destruct (a \in F);
  inversion H1 || lra).
  assert (
    \sum_(i0 in finset (T:=U) (preim X (pred1 i))) X i0 * Ind (A:=U) F i0 * P i0 =
    \sum_(i0 in finset (T:=U) (preim X (pred1 i)) :&: F) X i0 * Ind (A:=U) F i0 * P i0 +
    \sum_(i0 in finset (T:=U) (preim X (pred1 i)) :\: F) X i0 * Ind (A:=U) F i0 * P i0
  ).
  apply big_setID.
  rewrite H1 in H2.
  rewrite Rplus_0_r in H2.
  rewrite <- H2.
  apply eq_bigl.
  unfold eqfun.
  intros.
  rewrite in_set.
  simpl. auto.
  rewrite H.
  rewrite <- sum_parti_finType.
  auto.
Qed.

Lemma Cauchy_Schwarz_proba
  (X Y: {RV P -> R}): 
    Rsqr (`E (X `* Y: {RV P -> R})) <= `E (X `^2) * `E (Y `^2).
Proof.
  Admitted.

Lemma I_square F: Ind (A:=U) F = ((Ind (A:=U) F) `^2 : {RV P -> R}).
Proof.
  apply functional_extensionality; unfold Ind; intros x.
  by destruct (x \in F) eqn:H0;
  unfold "`^2", "`o";
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
  apply Rle_0_sqr.
  apply FDist.ge0.
Qed.

(*prove A1 and A3 for later use*)
Lemma cEx_var (X : {RV P -> R}) F : 0 < Pr P F  -> 
  `| `E_[ X | F ] - `E X | <= sqrt (`V X / Pr P F ).
Proof.
  intros.
  assert (0 <= / Pr P F) as PrPF_pos.
  apply Rlt_le.
  apply invR_gt0.
  auto.
  assert ( Rabs ( `E_[ X | F ] - `E X )  =  Rabs (`E ((X `-cst `E X) `* Ind F: {RV P -> R})) / Pr P F ).
  { unfold Rdiv.
    rewrite <- (Rabs_pos_eq (/Pr P F)).
    rewrite <- (Rabs_mult).
    apply congr1.
    assert (((X `-cst `E X) `* Ind (A:=U) F) = (X `* Ind (A:=U) F `- `E X `cst* Ind (A:=U) F : {RV P -> R})).
    apply functional_extensionality.
    intros. unfold "`-", "`cst*", "`-cst".
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
    apply Rplus_eq_compat_r.
    apply cEx_EXInd.
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
    destruct (u \in F).
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
    - apply functional_extensionality. unfold "`^2". simpl. unfold "`o".
    unfold Ind.
    intros. simpl. 
    destruct (x \in F). lra. lra.
    
    rewrite H2. 
    - assert (((X `-cst `E X) `^2) `* Ind (A:=U) F =
    (((X `-cst `E X) `* Ind (A:=U) F) `^2: {RV P -> R})).
    rewrite I_square.
    apply functional_extensionality.
    intros.
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
       rewrite <- (Rplus_eq_reg_r (Pr P (~: F) * `E_[X | (~: F)])   (`E_[X | F] * Pr P F)  ).
        *** lra.
        *** rewrite Rplus_assoc.
            rewrite (Rplus_opp_l (Pr P (~: F) * `E_[X | (~: F)]) ).
            rewrite Rplus_0_r.
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

            destruct (i \in F).
            rewrite addR0. lra.
            lra.
                  + rewrite Pr_of_cplt. lra. 
                  + (*Pr P F <> 0*) lra.

      ** (*-1 <> 0*) lra.
      ** (*0 <= 1 - Pr P F*) lra.
      ** (*0 <= Pr P F*) lra.
    * (*Pr P F <> 0*) lra.
  - (*Pr P F <> 0*) lra.
Admitted.  

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
    apply leR_pmul; try (apply Rlt_le; apply invR_gt0); try lra.
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

End probability.

Infix ">=?" := Rgeb : R_scope.

Theorem robust_mean
  (U: finType)
  (P: fdist U)
  (good elim: {set U})
  (X Y: {RV P -> R})
  (eps: R):
  let bad := ~: good in
  let XY := (X `* Ind good) `+ (Y `* Ind bad) : {RV P -> R} in
  let mu_hat := `E_[ XY | ~: elim ] in
  let mu := `E X in
  `E_[ X | good ] = mu ->
  0 < eps -> eps <= 1/8 ->
  Pr P bad = eps -> Pr P elim = 4 * eps ->
  (* All the outliers exceeding the ε-quantile are eliminated: *)
  [ set y in bad | `| Y y - mu | >=? sqrt (`V X / eps) ] \subset elim ->
  `| mu_hat - mu | <=  8 * sqrt (`V X / eps).
Proof.
  intros bad XY mu_hat mu EX_good
    Hmin_outliers Hmax_outliers Hbad_ratio Helim_ratio Hquantile_elim_bad.
  assert (Pr P good = 1 - eps).
  {
    rewrite <- Ropp_involutive.
    rewrite <- Ropp_involutive at 1.
    apply Ropp_eq_compat.
    apply (Rplus_eq_reg_l 1).
    assert (1 + - Pr P good = 1 - Pr P good).
    auto.
    rewrite H.
    rewrite <- Pr_of_cplt.
    rewrite Hbad_ratio. nra.
  }
  (* On the other hand, we remove at most 4ε good points *)
  assert (Pr P (good :&: elim) <= 4 * eps) as Hmax_good_elim.
  {
    rewrite <- Helim_ratio.
    apply Pr_incl.
    apply subsetIr.
  }
  (* Remaining good points: 1 - (4 * eps) / (1 - eps) *)
  pose (delta := 1 - (4 * eps) / (1 - eps)).
  assert (delta <= Pr P (good :\: elim)) as Hmin_good_remain.
  {
    admit.
  }
  assert (`E_[ X | good ] = `E_[ XY | good ]).
  {
    repeat rewrite cEx_EXInd. unfold Rdiv. 
    apply Rmult_eq_compat_r.
    unfold "`E".
    unfold ambient_dist.
    apply congr_big.
    auto. auto.
    intros. simpl.
    unfold XY.
    repeat unfold "`*", "`+", "`*cst".
    repeat rewrite <- Rmult_assoc.
    apply Rmult_eq_compat_r.
    repeat unfold Ind.
    unfold bad.
    rewrite in_setC.
    destruct (i \in good); simpl; nra.
  }
  assert (
    `| `E_[X | good :\: elim ] - `E X | <= sqrt (`V X * 2 * (1 - delta) / delta)
  ).
  {
    apply resilience.
    unfold delta.
    apply (Rplus_lt_reg_r (4 * eps / (1 - eps))).
    rewrite Rplus_assoc.
    rewrite Rplus_opp_l.
    rewrite Rplus_0_l.
    rewrite Rplus_0_r.
    apply (Rmult_lt_reg_r (1-eps)).
    nra.
    unfold Rdiv.
    rewrite Rmult_assoc.
    rewrite Rinv_l.
    nra.
    nra.
    nra.
    apply Rle_lt_trans with (r2 := Pr P good).
    apply Pr_incl.
    apply subsetDl.
    nra.
  }
  assert (
    `| `E_[ XY | bad :\: elim ] - `E X | <= sqrt (`V X / eps)
  ).
  {
    admit.
  }
  assert (
    Pr P (bad :\: elim) <= eps / (1 - 4 * eps)
  ).
  {
    admit.
  }
  assert (
    `E_[ XY | ~: elim ]  =
      (`E_[ XY | good :\: elim ] * Pr P (good :\: elim) 
      + `E_[ XY | bad :\: elim ] * Pr P (bad :\: elim)) / Pr P (~: elim)
  ).
  {
    apply (Rmult_eq_reg_r (Pr P (~: elim))).
    repeat rewrite cEx_EXInd.
    repeat rewrite Rmult_assoc.
    repeat rewrite Rinv_l.
    (* we should make the case when bad :\: elim = empty and good :\: elim = empty *)
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
    destruct (i \in elim).
    simpl. lra.
    simpl.
    unfold bad. rewrite in_setC.
    destruct (i \in good); simpl; nra.
    admit. admit. (* these should be handled earlier *)
    all: rewrite Pr_of_cplt; nra.
  }
  assert (
    `E_[ X | good :\: elim ] = `E_[ XY | good :\: elim ]
  ).
  {
    repeat rewrite cEx_EXInd.
    apply Rmult_eq_compat_r.
    apply congr_big.
    auto. auto.
    intros.
    unfold ambient_dist.
    repeat rewrite Rmult_assoc.
    unfold XY, Ind, "`*cst", "`+".
    rewrite in_setD. rewrite in_setC.
    unfold "\notin".
    destruct (i \in good);
    destruct (i \in elim); simpl.
    all: nra.
  }
  rewrite H5 in H1.
Admitted.




(* σ = sqrt (V X) -- the sqrt variance
   μ = E X        -- the mean
*

Theorem robust_mean
  (bad good elim: {set U})
  (X: {RV P -> R})
  (alpha eps: R):
  let mu := `E_[ X | good ] in
  let mu_bar := `E X in
  let mu_hat := `E_[ X | ~: elim ] in
  eps <= 1/8 ->
  Pr P elim = 4 * eps ->
  [ set x : U | `| X x - mu_bar | >=? sqrt (`V X / (4 * eps)) ] \subset elim ->
  finset.partition [set bad; good] [set: U] ->
  Pr P bad = eps ->
  `| mu_hat - mu | <=  8 * sqrt (`V X / eps).
Proof.
Theorem robust_mean (U: finType)
  (P: fdist U)
  (X : {RV P -> R})
  (alpha eps: R):
    let F := [ set x : U | Rleb (`| X x - `E X |) (sqrt (`V X / eps)) ] in
    let mu' := `E_[ X | F ] in
    let mu  := `E X in
    eps > 0 -> eps < 1/8 ->
      `| mu' - mu | <= 8 * sqrt (`V X * eps).
Proof.
  intros.
  unfold mu, mu'.
  assert (Pr P F <= eps).
  admit.
  assert (sqrt (2 * (1-eps) / eps) <= sqrt (64 * eps)).
  apply sqrt_le_1.
  admit.
  lra.
  apply (Rmult_le_reg_r eps).
  lra.
  unfold Rdiv.
  repeat rewrite Rmult_assoc; rewrite Rinv_l.
  rewrite Rmult_1_r.
  apply Rmult_le_compat_l.
  lra.
  unfold Rminus.
  apply (Rplus_le_reg_r eps).
  rewrite Rplus_assoc.
  rewrite Rplus_opp_l.
*)


Require Import List.
Require Import Sorting.
Require Import Orders.

Definition Average l := fold_left Rplus l 0 / INR (length l).

Module ROrder <: TotalLeBool.
  Definition t := R.
  Definition leb := Rleb.
  Lemma leb_total : forall x y : t, leb x y = true \/ leb y x = true.
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