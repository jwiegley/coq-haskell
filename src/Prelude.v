Require Export Hask.Ssr.
Require Import Hask.Ltac.
Require Export Hask.Data.Either.
Require Export Hask.Data.Maybe.
Require Export Hask.Data.Tuple.
Require Export Hask.Data.Functor.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition undefined {a : Type} : a. Admitted.

Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).

Definition flip `(f : a -> b -> c) : b -> a -> c := fun y x => f x y.

Definition const {A B : Type} (x : B) : A -> B := fun _ => x.

Definition apply `(f : a -> b) (x : a) : b := f x.

Definition compose {a b c : Type} (f : b -> c) (g : a -> b) : a -> c := f \o g.

Lemma compA {a b c d : Type} (h : a -> b) (g : b -> c) (f : c -> d) :
  (f \o g) \o h =1 f \o (g \o h).
Proof. done. Qed.

Definition lebf {a : Type} (f : a -> nat) (n m : a) := f n <= f m.

Definition oddnum := { n : nat | odd n }.

Program Definition odd1 := exist odd 1 _.

Lemma odd_gt1 : forall n, odd n -> n >= 1.
Proof. by elim. Qed.

Lemma odd_double_plus (n : nat) : odd n.*2.+1.
Proof.
  elim: n => [|n IHn] //=.
  apply/negPn.
  by rewrite odd_double.
Qed.

Lemma isP : forall x : bool, x = true -> x.
Proof. by []. Qed.

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

Lemma ltn_plus : forall m n, 0 < n -> m < m + n.
Proof. by elim. Qed.

Lemma leq_plus : forall m n, m <= m + n.
Proof. by elim. Qed.

Lemma leq_eqF : forall n m, (n == m) = false -> n <= m -> n < m.
Proof.
  move=> n m.
  move/eqP=> H1 H2.
  by ordered.
Qed.
