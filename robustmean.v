From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg matrix.
From mathcomp Require boolp.
From mathcomp Require Import Rstruct.
Require Import Reals Lra ROrderedType.
From infotheo Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext.
From infotheo Require Import Rbigop proba fdist.

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

Lemma Ind_ge0 (X : {set U}) (x : U) : 0 <= Ind X x.
Proof. by rewrite /Ind; case: ifPn. Qed.

Lemma cEx_EXInd (X : {RV P -> R}) F :
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
rewrite boolp.funeqE /Ind => x.
by rewrite /sq_RV /comp_RV /=; case: ifPn => xF /=; rewrite ?(mulR0,mulR1).
Qed.

Lemma I_double F : Ind F = ((Ind F) `* (Ind F) : {RV P -> R}).
Proof.
by rewrite [LHS]I_square boolp.funeqE => u; rewrite /sq_RV /comp_RV mulRR.
Qed.

(*
Lemma I_mult_one F : (Ind (A:=U) F : {RV P -> R}) `* 1 = Ind (A:=U) F.
(F: {RV P -> R}): (Ind (A:=U) F: {RV P -> R}) `* 1 = (Ind (A:=U) F : {RV P -> R}). *)

Lemma variance_nonneg (X : {RV P -> R}) : 0 <= `V X.
Proof.
by apply: sumR_ge0 => u _; apply mulR_ge0 => //; apply: sq_RV_ge0.
Qed.

(*prove A1 and A3 for later use*)
Lemma cEx_var (X : {RV P -> R}) F : 0 < Pr P F  ->
  `| `E_[ X | F ] - `E X | <= sqrt (`V X / Pr P F ).
Proof.
move=> PF_gt0.
have PrPF_pos : 0 <= / Pr P F by apply/Rlt_le/invR_gt0.
have -> : `| `E_[ X | F ] - `E X | =
         `| (`E ((X `-cst `E X) `* Ind F: {RV P -> R})) | / Pr P F.
  rewrite /Rdiv -(Rabs_pos_eq (/Pr P F)); last exact/PrPF_pos.
  rewrite -(Rabs_mult);  congr (`| _ |).
  have -> : (X `-cst `E X) `* @Ind U F =
           (X `* @Ind U F `- `E X `cst* @Ind U F : {RV P -> R}).
    by apply boolp.funext => u; unfold "`-", "`cst*", "`-cst"; lra.
  rewrite E_sub_RV mulRDl E_scalel_RV E_Ind mulNR -mulRA.
  rewrite Rinv_r ?mulR1; last exact/eqP/gtR_eqF.
  exact/Rplus_eq_compat_r/cEx_EXInd.
have H0 : 0 <= `E ((X `-cst `E X) `^2 `* @Ind U F : {RV P -> R}) *
              `E (@Ind U F : {RV P -> R}).
  apply: mulR_ge0; last by rewrite E_Ind; exact: Pr_ge0.
  apply: Ex_ge0 => u; apply: mulR_ge0; [exact: sq_RV_ge0|].
  by rewrite /Ind; case: ifPn.
apply (@leR_trans (sqrt (mknonnegreal (`E (((X `-cst `E X) `^2) `*
                                          @Ind U F : {RV P -> R}) *
                                       `E (@Ind U F : {RV P -> R})) H0) / Pr P F)).
  rewrite /Rdiv; apply leR_pmul2r; first exact/invR_gt0.
  rewrite -sqrt_Rsqr_abs; apply sqrt_le_1_alt => /=.
  have -> : (X `-cst `E X ) `* ((@Ind U F : {RV P -> R})) =
      (X `-cst `E X) `* (@Ind U F : {RV P -> R}) `* (@Ind U F : {RV P -> R}).
    by rewrite [in LHS]I_double boolp.funeqE => x; rewrite mulRA.
  have -> : ((X `-cst `E X) `^2) `* @Ind U F =
      (((X `-cst `E X) `* @Ind U F) `^2 : {RV P -> R}).
    rewrite I_square; apply boolp.funext => u.
    by rewrite {1}I_square /sq_RV /comp_RV /=; lra.
  by rewrite -> I_square at 1; exact: Cauchy_Schwarz_proba.
rewrite /nonneg /Rdiv -(sqrt_Rsqr (/ Pr P F)) // -sqrt_mult_alt //.
apply sqrt_le_1_alt.
rewrite /Var sqrt_Rsqr // /Rsqr mulRA leR_pmul2r; last exact/invR_gt0.
rewrite E_Ind -mulRA Rinv_r ?mulR1; last exact/eqP/gtR_eqF.
apply leq_sumR => u uU.
rewrite /Ind; case: (u \in F); first by unfold ambient_dist; lra.
by rewrite mulR0 mul0R; apply: mulR_ge0; [exact: sq_RV_ge0|exact: FDist.ge0].
Qed.

Lemma cEx_cptl (X: {RV P -> R}) F:
  0 < Pr P F -> Pr P F < 1 ->
    `E_[X | F] * Pr P F + `E_[X | (~: F)] * Pr P (~: F) = `E X.
Proof.
  move => PrFgt0 PrFlt1.
  repeat rewrite cEx_EXInd.
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
  repeat rewrite cEx_EXInd.
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

Lemma cEx_Inv (X: {RV P -> R}) F :
  0 < Pr P F -> Pr P F < 1 ->
  `| `E_[X | F] - `E X| = (1 - Pr P F) / Pr P F * `| `E_[X | (~: F)] - `E X|.
Proof.
  move => H H0.
  have PrF_ne0: Pr P F <> 0 by lra.
  apply (eqR_mul2l PrF_ne0).
  rewrite mulRA.
  have ->: Pr P F * ((1 - Pr P F) / Pr P F) = 1 - Pr P F.
  rewrite mulRC -mulRA mulVR; last by apply Pr_gt0. by rewrite mulR1.
  rewrite -Pr_of_cplt.
  have: 0 <= `E_[X | F] - `E X \/ `E_[X | F] - `E X < 0 by apply Rle_or_lt.
  case => [Hdiff_ge0|Hdiff_lt0].
  - rewrite geR0_norm; last by [].
    rewrite cEx_Inv_int; try lra.
    rewrite leR0_norm. auto.
    apply Rmult_le_compat_l with (r:= Pr P F) in Hdiff_ge0; last lra.
    rewrite mulR0 in Hdiff_ge0.
    rewrite cEx_Inv_int in Hdiff_ge0; try lra.
    rewrite -(Rmult_0_r (Pr P (~:F))) in Hdiff_ge0.
    apply Rmult_le_reg_l in Hdiff_ge0; last rewrite Pr_of_cplt; lra.
  - rewrite ltR0_norm; last by [].
    rewrite mulRN cEx_Inv_int; try lra.
    rewrite mulRN oppRK.
    rewrite gtR0_norm. auto.
    apply Rmult_lt_compat_l with (r:= Pr P F) in Hdiff_lt0; last lra.
    rewrite mulR0 in Hdiff_lt0.
    rewrite cEx_Inv_int in Hdiff_lt0; try lra.
    rewrite -(Rmult_0_r (Pr P (~:F))) in Hdiff_lt0.
    apply Rmult_lt_reg_l in Hdiff_lt0; last rewrite Pr_of_cplt; lra.
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
    rewrite -Rmult_assoc. 
    apply leR_pmul; try (apply/Rlt_le/invR_gt0); try lra.
    apply leR_inv. assumption. 
    lra.
  }

  { (*Prob > 1/2 and delta < Probability*)
    rewrite cEx_Inv.
    (*Search (?x <= ?y -> ?y <= ?z -> ?x <= ?z).*)
    apply Rle_trans with (r2 := ((1 - Pr P F) / Pr P F * sqrt (`V X / Pr P (~: F)))).
    have H3 : 0 < Pr P F. lra.
    
    apply Rmult_le_compat_l.
    - apply divR_ge0; lra.
    - apply cEx_var; rewrite Pr_of_cplt; lra.
    
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
    have PrPF_pos : 0 <= / Pr P F. 
     by apply/Rlt_le/invR_gt0.
    
    have -> : ( `| `E_[ X | F ] - mu |  =  `| `E ((X `-cst mu) `* Ind F: {RV P -> R}) | / Pr P F ).
     rewrite divRE.
      rewrite -(geR0_norm (/Pr P F)) //.
       rewrite -normRM.
       apply congr1.
       have -> :  ((X `-cst mu) `* Ind (A:=U) F) = (X `* Ind (A:=U) F `- mu `cst* Ind (A:=U) F : {RV P -> R}).
        apply boolp.funext=> u.
        rewrite /sub_RV /scalel_RV /trans_min_RV.
        lra.
       rewrite E_sub_RV mulRDl E_scalel_RV E_Ind mulNR
               -mulRA mulRV ?gtR_eqF // mulR1.
       by apply/Rplus_eq_compat_r/cEx_EXInd.
    have H2 : (0 <= (`E ((X `-cst mu) `^2 `* Ind (A:=U) F: {RV P -> R}) * `E (Ind (A:=U) F:{RV P -> R}))).
      apply mulR_ge0.
       apply Ex_ge0 => u.
       by apply mulR_ge0; [apply pow2_ge_0 | apply Ind_ge0].
      by rewrite E_Ind.
    pose y :=
      sqrt (
            (`E (((X `-cst mu) `^2)
                   `* Ind (A:=U) F: {RV P -> R})
             * `E (Ind (A:=U) F:{RV P -> R}))
            )
           / Pr P F.
    apply leR_trans with (y := y).
    { unfold Rdiv.  
      apply Rmult_le_compat_r.
      apply PrPF_pos.
      rewrite -sqrt_Rsqr_abs.
      apply sqrt_le_1_alt.
      simpl.
      have H1: ( (X `-cst mu ) `* ((Ind (A:=U) F : {RV P -> R}) )  =
      (X `-cst mu)  `*  (Ind (A:=U) F : {RV P -> R})  `*  (Ind (A:=U) F : {RV P -> R}) :> {RV (P) -> (R)}).
      - apply boolp.funext=> u. rewrite /sq_RV/comp_RV/=.
      unfold Ind.
      simpl. 
      case : ifPn. lra. lra.
      rewrite H1.
      - assert (((X `-cst mu) `^2) `* Ind (A:=U) F =
      (((X `-cst mu) `* Ind (A:=U) F) `^2: {RV P -> R})).
      rewrite I_square.
      apply boolp.funext=> u.
      rewrite -> I_square at 1.
      rewrite /sq_RV/comp_RV/=.
      lra.
      - rewrite H3.
      rewrite -> I_square at 1.
      apply Cauchy_Schwarz_proba.
    }
    { 
      rewrite /y !divRE.
      rewrite -(sqrt_Rsqr (/ Pr P F)) //.
      rewrite -sqrt_mult_alt //.
      apply sqrt_le_1_alt.
      rewrite /var /cVar cEx_EXInd.
      rewrite sqrt_Rsqr /Rsqr // mulRA.
      apply leR_wpmul2r; first by apply PrPF_pos.
      rewrite E_Ind -!mulRA mulRV ?gtR_eqF // mulVR ?mulR1;
        last by rewrite ?gtR_eqF //; apply/(ltR_leR_trans H)/Pr_incl.
      apply leq_sumR => i iU.
      rewrite /Ind /ambient_dist /mu.
      apply leR_wpmul2r => //.
      apply leR_wpmul2l; first exact: sq_RV_ge0.
      case : ifPn => HiF.
      have -> // : i \in G.
        rewrite -sub1set.
        apply: subset_trans; last exact H0.
        by rewrite sub1set.
      by case (i \in G).
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
  repeat rewrite -Rmult_assoc.
  rewrite Rinv_r.
  rewrite Rmult_1_l.
  rewrite -(Rabs_pos_eq (Pr _ F)).
  rewrite -(Rabs_pos_eq (Pr _ (G :\: F))).
  repeat rewrite -Rabs_mult.
  rewrite Rmult_comm.
  rewrite (Rmult_comm (Pr P (G :\: F))).
  repeat rewrite cEx_EXInd.
  unfold Rminus.
  repeat rewrite Rmult_plus_distr_r.
  repeat rewrite Rmult_assoc.
  repeat rewrite Rinv_l.
  repeat rewrite mulR1.
  rewrite -Rabs_Ropp.
  apply congr1.
  apply Rplus_eq_reg_r with (r := 
  (`E (X `* Ind (A:=U) F : {RV P -> R}) + - (`E (X `* Ind (A:=U) G : {RV P -> R}) / Pr P G) * Pr P F)).
  rewrite Rplus_opp_l.
  repeat rewrite -Rplus_assoc.
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
  rewrite -big_split.
  simpl.
  rewrite Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite addR0.
  rewrite Rmult_assoc.
  rewrite Rinv_l.
  rewrite mulR1.
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
  rewrite -Rmult_plus_distr_r.
  apply Rmult_eq_compat_r.
  rewrite -Rmult_plus_distr_l.
  unfold Ind.
  rewrite in_setD.
  unfold "\notin".
  destruct (i \in F) eqn:HiF.
  assert (i \in G) as HiG.
  rewrite -sub1set.
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
  rewrite /sq_RV/comp_RV/=.
  unfold "^".
  apply mulR_ge0.
  rewrite mulR1.
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
      rewrite mulR1.
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
      rewrite mulR1 in H0.
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
      repeat rewrite -(Rmult_assoc).
      assert (Pr P G * / Pr P F * delta * Pr P F * / Pr P G =
      delta * (Pr P G * / Pr P G) * (Pr P F * / Pr P F)).
      lra.
      rewrite H4.
      repeat rewrite Rinv_r; repeat rewrite mulR1.
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

      rewrite -(Rabs_pos_eq (Pr P (G :\: F) / Pr P F)).
      rewrite -sqrt_Rsqr_abs;
      rewrite -sqrt_mult_alt.
      apply sqrt_le_1_alt.
      unfold Rdiv.
      repeat rewrite -Rmult_assoc.
      rewrite (Rmult_comm _  (`V_[X | G])).
      repeat rewrite Rmult_assoc;
      apply Rmult_le_compat_l. 
  
      apply cvariance_nonneg. auto.

      repeat rewrite -Rmult_assoc.
      rewrite Rmult_comm.
      repeat rewrite -Rmult_assoc.
      rewrite Rinv_l.
      rewrite Rmult_1_l.
      rewrite Rmult_comm.
      rewrite (Rmult_comm (/Pr P F)).
      rewrite Rmult_assoc.
      rewrite -Rinv_mult_distr.
      rewrite -Rmult_assoc.
      apply Rmult_le_reg_r with (r:=Pr P F * Pr P F).
      nra.
      rewrite Rmult_assoc.
      rewrite Rinv_l.
      rewrite mulR1.
      rewrite Rmult_assoc.
      rewrite (Rmult_comm (/ _)).
      rewrite <-Rmult_assoc.
      apply Rmult_le_reg_r with (r:= Pr P G * delta * delta).
      apply Rmult_lt_0_compat.
      nra. lra.
      rewrite (Rmult_assoc _ (/ _)).
      rewrite Rinv_l.
      rewrite mulR1.
      apply Rmult_le_compat_r with (r:= Pr P G) in H0.
      rewrite Rmult_assoc in H0.
      rewrite Rinv_l in H0.
      rewrite mulR1 in H0.
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
      rewrite -Rmult_assoc.
      apply Rmult_le_compat_r.
      apply/Rlt_le/Rinv_0_lt_compat.
      lra.
      repeat rewrite Rmult_assoc.
      apply Rmult_le_compat_l.
      apply cvariance_nonneg.
      lra.
      rewrite Rinv_mult_distr.
      rewrite -Rmult_assoc.
      rewrite (Rmult_comm (Pr P G)).
      rewrite -Rmult_assoc.
      rewrite (Rmult_assoc (1 - delta)).
      rewrite Rinv_r.
      rewrite mulR1.
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

(* TODO: move *)
Lemma eqR_divl_mulr (z x y : R) : z != 0 -> (x = y / z) <-> (x * z = y).
Proof. by move=> z0; split; move/esym/eqR_divr_mulr => /(_ z0) ->. Qed.

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
  - apply resilience'.
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
  rewrite 2!cEx_EXInd -addR_opp -mulNR mulRA -I_double -mulRDl big_distrr /=.
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
    rewrite 2!cEx_EXInd good_bad; congr (_ / _).
    apply/eq_bigr => u _.
    rewrite /ambient_dist -!mulRA; congr (_ * _).
    (* NB: lemma? *)
    rewrite /Ind !inE.
    have bad_drop0 : u \in bad :\: drop -> P u = 0 by apply Pr_set0P.
    case: ifPn => idrop //=.
    by case: ifPn => // igood; rewrite bad_drop0 ?mulR0// !inE idrop.
  - apply/eqR_divl_mulr; first by rewrite Pr_of_cplt; apply/eqP; nra.
    rewrite !cEx_EXInd -!mulRA.
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
