Require Import Hask.Prelude.
Require Import Hask.Data.List.
Require Import Hask.Data.NonEmpty.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Inductive IntSet := getIntSet of seq nat.

Arguments getIntSet _.

Definition emptyIntSet := getIntSet [::].

Definition IntSet_singleton (x : nat) := getIntSet [:: x].

(* We needn't bother defining these in Coq, since they only matter to the
   extracted Haskell code, and there we use the definitions from
   [Data.IntMap]. *)
Definition IntSet_member : nat -> IntSet -> bool :=
  fun k m => let: getIntSet xs := m in k \in xs.

Definition IntSet_size : IntSet -> nat :=
  fun m => let: getIntSet xs := m in size xs.

Definition IntSet_insert : nat -> IntSet -> IntSet := fun k m =>
  let: getIntSet xs := m in
  if k \in xs then m else getIntSet (k :: xs).

Definition IntSet_delete : nat -> IntSet -> IntSet := fun k m =>
  let: getIntSet xs := m in getIntSet (rem k xs).

Definition IntSet_union : IntSet -> IntSet -> IntSet := fun m1 m2 =>
  let: getIntSet xs1 := m1 in
  let: getIntSet xs2 := m2 in
  getIntSet (undup (xs1 ++ xs2)).

Definition IntSet_difference : IntSet -> IntSet -> IntSet := fun m1 m2 =>
  let: getIntSet xs1 := m1 in
  let: getIntSet xs2 := m2 in
  getIntSet (filter (fun k => k \notin xs2) xs1).

Definition IntSet_foldl : forall a, (a -> nat -> a) -> a -> IntSet -> a :=
  fun _ f z m => let: getIntSet xs := m in foldl f z xs.

Definition IntSet_forFold {a} (z : a) (m : IntSet) (f: a -> nat -> a) : a :=
  IntSet_foldl f z m.

Definition IntSet_toList (m : IntSet) : seq nat :=
  let: getIntSet xs := m in xs.

Section EqIntSet.

Variable a : eqType.

Definition eqIntSet (s1 s2 : IntSet) :=
  match s1, s2 with
  | getIntSet xs, getIntSet ys => xs == ys
  end.

Lemma eqIntSetP : Equality.axiom eqIntSet.
Proof.
  move.
  case=> [s1].
  case=> [s2] /=.
  case: (s1 =P s2) => [<-|neqx]; last by right; case.
  by constructor.
Qed.

Canonical IntSet_eqMixin := EqMixin eqIntSetP.
Canonical IntSet_eqType := Eval hnf in EqType IntSet IntSet_eqMixin.

End EqIntSet.
