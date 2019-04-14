Require Import Hask.Ltac.
Require Export Hask.Data.Either.
Require Export Hask.Data.Maybe.
Require Export Hask.Data.Tuple.
Require Export Hask.Data.Functor.
Require Export Omega.
Require Import Coq.Classes.Equivalence.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Infix "≈" := equiv (at level 48).

Definition undefined {a : Type} : a. Admitted.

Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).

Definition flip `(f : a -> b -> c) : b -> a -> c := fun y x => f x y.

Definition const {A B : Type} (x : B) : A -> B := fun _ => x.

Definition apply `(f : a -> b) (x : a) : b := f x.

Definition compose {a b c : Type} (f : b -> c) (g : a -> b) : a -> c := f \o g.

Lemma compA {a b c d : Type} (h : a -> b) (g : b -> c) (f : c -> d) :
  (f \o g) \o h = f \o (g \o h).
Proof. reflexivity. Qed.

Notation "f .: g" := (fun x y => f (g x y)) (at level 100).

(*
Lemma sym_neg : forall a (R : rel a), symmetric R -> symmetric (negb .: R).
Proof.
  move=> a R H x y.
  by rewrite H.
Qed.
*)

Definition lebf {a : Type} (f : a -> nat) (n m : a) := f n <= f m.

(*
Definition oddnum := { n : nat | odd n }.

Program Definition odd1 := exist odd 1 _.

Lemma odd_gt1 : forall n, odd n -> n >= 1.
Proof. by elim. Qed.

Lemma odds1 : forall n, odd n -> ~~ odd (n.-1).
Proof. by elim. Qed.

Lemma odd_double_plus (n : nat) : odd n.*2.+1.
Proof.
  elim: n => [|n IHn] //=.
  apply/negPn.
  by rewrite odd_double.
Qed.

Lemma isP : forall x : bool, x = true -> x.
Proof. by []. Qed.

Lemma has_over_false A (f : A -> bool) (xs : seq A) :
   has (fun x => f x || false) xs = has f xs.
Proof.
  elim: xs => //= [x xs IHxs].
  by rewrite !Bool.orb_false_r IHxs.
Qed.

Lemma has_flip A (R : rel A) (_ : symmetric R) (xs ys : seq A) :
  has (fun x => has (fun y => R x y) ys) xs
    = has (fun y => has (fun x => R y x) xs) ys.
Proof.
  elim: xs => /= [|x xs IHxs].
    by elim: ys.
  rewrite has_predU {}IHxs.
  f_equal.
  elim: ys => //= [y ys IHys].
  by rewrite IHys H.
Qed.

Lemma ltn_odd n m : odd n && odd m -> n < m -> n.+1 < m.
Proof.
  move/andP=> [nodd modd] Hlt.
  rewrite -subn_gt0 odd_gt0 // odd_sub // modd /=.
  exact/negPn.
Qed.

Lemma odd_minn : forall x y, odd x -> odd y -> odd (minn x y).
Proof.
  move=> x y Hx Hy.
  rewrite /minn.
  by case: (x < y).
Qed.

Definition distance (n m : nat) : nat := if n < m then m - n else n - m.
*)

Lemma ltn_plus : forall m n, 0 < n -> m < m + n.
Proof. intros; omega. Qed.

Lemma leq_plus : forall m n, m <= m + n.
Proof. intros; omega. Qed.

Lemma leq_add2r : forall p m n : nat, m <= n -> m + p <= n + p.
Proof. intros; omega. Qed.

Lemma leq_add2l : forall p m n : nat, m <= n -> p + m <= p + n.
Proof. intros; omega. Qed.

(*
Lemma leq_eqF : forall n m, (n == m) = false -> n <= m -> n < m.
Proof.
  move=> n m.
  move/eqP=> H1 H2.
  by ordered.
Qed.

Lemma leq_double_r : forall n m, n <= m -> n <= m.*2.
Proof.
  move=> n m H.
  rewrite -muln2.
  have ->: n = n * 1 by ordered.
  exact: leq_mul.
Qed.
*)

Lemma ltn0ltn : forall n m, n < m -> 0 < m.
Proof. intros; omega. Qed.

Lemma ltn_subn : forall n m, n < m -> m > 0 -> n <= m - 1.
Proof. intros; omega. Qed.
