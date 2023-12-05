Require Import Setoid.

Class monad (M: Type -> Type) :=
  { ret {A}: A -> M A;
    bind {A B}: M A -> (A -> M B) -> M B;
    _: forall A B (x: A) (f: A -> M B), bind (ret x) f = f x;
    _: forall A (ma: M A), bind ma ret = ma;
    _: forall A B C (ma: M A) (f: A -> M B) (g: B -> M C), bind ma (fun x => bind (f x) g) = bind (bind ma f) g }.

Notation "E >>= F" := (bind E F) (at level 11, right associativity).

Notation "X <- E ; F" := (bind E (fun X => F)) (at level 11, right associativity).

Open Scope list_scope.

Inductive Proba {a: Type} := Outcome: list (nat * a) -> Proba.

Fixpoint uniform {a: Type} (xs: list a) := match xs with
| x :: xs =>
  match uniform xs with
  | Outcome os => Outcome ((1, x) :: os)
  end
| nil => Outcome nil
end.

Require Import List PeanoNat.

Fixpoint mulp {a} p (ys: list (nat * a)) := match ys with
  nil => nil
| (p', y)::ys' => (p*p', y)::mulp p ys'
end.

Lemma mulp_1 {a} (ys: list (nat * a)): mulp 1 ys = ys.
Proof.
    induction ys.
    - auto.
    - (*Search (mulp 1).*) simpl. case a0. 
      intros. (*Search (?x+0).*) 
      rewrite <-plus_n_O. 
      rewrite IHys. apply eq_refl. 
Qed.

Lemma mulp_xy {a} x y (l: list (nat * a)):
  mulp x (mulp y l) = mulp (x * y) l.
Proof.
  induction l.
  - auto.
  - case a0. intros. simpl. rewrite IHl. 
  (*Search _ "assoc".*)
  rewrite Nat.mul_assoc. apply eq_refl. 
Qed.

Lemma mulp_concat {a} x (l1 l2: list (nat * a)):
  mulp x l1 ++ mulp x l2 = mulp x (l1 ++ l2).
Proof.
  induction l1.
  - (*Search (nil ++ _).*) apply app_nil_l.
  - simpl. case a0. intros. rewrite <-IHl1. apply eq_refl. 
Qed.


Fixpoint bindx {a b} (xs: list (nat * a)) (f: a -> @Proba b) := match xs with
  nil => Outcome nil
| (p, x)::xs' =>
    let 'Outcome y := f x in 
    let 'Outcome ys' := bindx xs' f in
    Outcome (mulp p y ++ ys')
end.

Program Instance proba_monad : monad (@Proba) :=
  {
      ret _ x := Outcome ((1, x) :: nil);
      bind _ _ os f := let 'Outcome xs := os in bindx xs f
  }.


Next Obligation.
destruct (f x).
rewrite mulp_1.
rewrite app_nil_r.
auto.
Qed.

Next Obligation.
destruct ma.
induction l.
- auto.
- simpl. destruct a. rewrite IHl. rewrite Nat.mul_1_r. auto.
Qed.

Next Obligation.
destruct ma.
induction l.
- simpl. auto.
- destruct a. simpl. rewrite IHl. 
  destruct (bindx l f), (f a).
  induction l1.
  + simpl. destruct (bindx l0 g). auto.
  + simpl mulp. destruct a0.
    rewrite <- app_comm_cons.
    simpl bindx. rewrite <- IHl1.
    destruct (g b).
    destruct (bindx l1 g).
    destruct (bindx l0 g).
    rewrite <- mulp_concat.
    rewrite <- mulp_xy.
    rewrite app_assoc.
    auto.
Defined.

Definition dice := uniform (1::2::3::4::5::6::nil).

Program Instance option_monad: monad option := {
  ret _ x := Some x;
  bind _ _ x f := match x with
    Some x => f x
  | None => None
  end
}.

Next Obligation.
destruct ma; auto.
Qed.

Next Obligation.
destruct ma; auto.
Qed.

(* Now diceTwice is polymorphic on the type of the monad *)
Definition diceTwice {m} {_: monad m} dice :=
    x <- dice; y <- dice; ret (x+y).
(*
  Alternative, equivalent definitions:
    dice >>= (fun x => dice >>= (fun y => ret (x + y))).
    bind dice (fun x => bind dice (fun y => ret (x+y))). *)

Check fold_left.
Definition probOf {a} m (f: a -> bool) :=
  let 'Outcome xs := m in
  fold_left (fun n '(p,y) => n + p) (filter (fun '(p,x) => f x) xs) 0.

Print diceTwice.
(* For example it can work on probability distributions *)
Compute (diceTwice dice).

Fixpoint range_ start stop xs :=
  if start =? stop then start::xs
  else match stop with
    (S x) => range_ start x (stop::xs)
  | 0 => stop::xs
  end.
Definition range start stop := range_ start stop nil.
Lemma rangeSn n: 1 <= n ->
  range 1 (S n) = range 1 n ++ (S n::nil).
Proof.
  intros H.
  induction n.
  - apply Nat.nle_succ_0 in H.
    contradiction.
  - destruct (n).
    + auto.
    + rewrite IHn. simpl.
      rewrite app_assoc_reverse.
      simpl.
      auto.
      Search ((_ ++ _) ++ _).

  simpl. auto.
Admitted.

Lemma mostProbableThrow n:
  forall m, 1 <= m <= n ->
  (probOf (diceTwice (uniform (range 1 n))) (fun x => x =? (1+m))) = m /\
  (probOf (diceTwice (uniform (range 1 n))) (fun x => x =? (2*n+1-m))) = m.
Proof.
  induction n.
  - intros m H.
    destruct m.
    auto.
    inversion H.
    apply Nat.nle_succ_0 in H1.
    contradiction.
  - intros m H.
    apply IHn in m.

Qed.

Require Extraction.

Extraction Language Haskell.

Extraction diceTwice.