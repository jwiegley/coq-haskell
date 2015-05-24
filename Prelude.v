Require Export Hask.Ssr.
Require Import Hask.Ltac.
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

Definition first `(f : a -> b) `(x : a * z) : b * z :=
  match x with (a, z) => (f a, z) end.

Definition second `(f : a -> b) `(x : z * a) : z * b :=
  match x with (z, b) => (z, f b) end.

Definition curry `(f : a -> b -> c) (x : (a * b)) : c :=
  match x with (a, b) => f a b end.

Definition isJust {a} (x : option a) := if x is Some _ then true else false.

Definition option_map `(f : a -> b) (x : option a) : option b :=
  match x with
  | None => None
  | Some x => Some (f x)
  end.

Definition option_choose {a} (x y : option a) : option a :=
  match x with
  | None => y
  | Some _ => x
  end.

Lemma rcons_nil : forall a us (u : a), rcons us u = [::] -> False.
Proof. by move=> a us u; case: us => // [|? ?] in u *. Qed.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Require String.
Open Scope string_scope.

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

Lemma lift_bounded : forall n (x : 'I_n), ord_max != widen_ord (leqnSn n) x.
Proof.
  move=> n.
  case=> /= m Hlt.
  rewrite /ord_max /lift.
  apply/eqP; invert.
  move: H0 Hlt => ->.
  by rewrite ltnn.
Qed.

Definition widen_id {n} := widen_ord (leqnSn n).
Arguments widen_id [n] i /.
Definition widen_fst {n a} p := (@widen_id n (@fst _ a p), snd p).

Lemma widen_ord_inj : forall m n (H : m <= n), injective (widen_ord H).
Proof.
  move=> m n H.
  rewrite /injective => x1 x2.
  by invert; apply ord_inj.
Qed.

Lemma widen_ord_spec : forall n x (H : n <= n), widen_ord H x = x.
Proof.
  move=> ? [? ?] ?.
  rewrite /widen_ord.
  congr (Ordinal _).
  exact: eq_irrelevance.
Qed.

Lemma widen_fst_inj : forall a n, injective (@widen_fst n a).
Proof.
  move=> a n.
  rewrite /injective => [[[x1a H1] x1b] [[x2a H2] x2b]].
  invert.
  congr (_, _).
  rewrite H0 in H1 *.
  congr (Ordinal _).
  exact: eq_irrelevance.
Qed.

Lemma and_swap : forall x y z, [&& x, y & z] = [&& y, x & z].
Proof. by case; case; case. Qed.

Lemma widen_ord_refl : forall n (H : n <= n) x, widen_ord (m := n) H x = x.
Proof.
  move=> n H.
  case=> m Hm.
  rewrite /widen_ord /=.
  congr (Ordinal _).
  exact: eq_irrelevance.
Qed.
