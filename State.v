Require Import Endo.
Require Import Applicative.
Require Import Monad.

Generalizable All Variables.

Section State.

Variable s : Type.

Inductive State (a : Type) := mkState : (s -> (a * s)) -> State a.

Arguments mkState [a] _.

Definition runState {a} (x : State a) := match x with mkState f => f end.

Global Program Instance State_Functor : Functor State := {
    fmap := fun _ _ f x =>
      mkState (fun st => let (a,st') := runState x st in (f a, st'))
}.
Obligation 1.
  extensionality x.
  destruct x.
  unfold id.
  f_equal.
  extensionality st.
  simpl.
  destruct (p st).
  reflexivity.
Qed.
Obligation 2.
  extensionality x.
  unfold compose.
  f_equal.
  extensionality y.
  destruct x.
  simpl.
  destruct (p y).
  reflexivity.
Qed.

Global Program Instance State_Applicative : Applicative State := {
    pure := fun _ x => mkState (fun st => (x, st));
    ap := fun _ _ f x =>
      mkState (fun st =>
        let (f', st') := runState f st in
        let (x', st'') := runState x st' in
        (f' x', st''))
}.
Obligation 1.
  extensionality x.
  destruct x.
  unfold id. simpl.
  f_equal.
  extensionality st.
  destruct (p st).
  reflexivity.
Qed.
Obligation 2.
  f_equal.
  extensionality st.
  destruct u.
  destruct v.
  destruct w.
  simpl.
  destruct (p st).
  destruct (p0 s0).
  destruct (p1 s1).
  unfold compose.
  reflexivity.
Qed.

Global Program Instance State_Monad : Monad State := {
    join := fun _ x => mkState (fun st =>
      let (y, st') := runState x st in
      let (a, st'') := runState y st' in
      (a, st''))
}.
Obligation 1.
  extensionality x.
  unfold compose.
  f_equal.
  extensionality y.
  destruct x. simpl.
  destruct (p y).
  destruct s0. simpl.
  destruct (p0 s1).
  destruct s0. simpl.
  destruct (p1 s2).
  reflexivity.
Qed.
Obligation 2.
  extensionality x.
  unfold compose, id.
  destruct x.
  f_equal. simpl.
  extensionality y.
  destruct (p y).
  reflexivity.
Qed.
Obligation 3.
  extensionality x.
  unfold compose, id.
  destruct x. simpl.
  f_equal.
  extensionality y.
  destruct (p y).
  reflexivity.
Qed.
Obligation 4.
  extensionality x.
  unfold compose.
  f_equal.
  extensionality y.
  destruct x. simpl.
  destruct (p y). simpl.
  destruct s0. simpl.
  destruct (p0 s1).
  reflexivity.
Qed.

Definition get : State s := mkState (fun s => (s, s)).

Definition gets {a} (f : s -> a) : State a := mkState (fun s => (f s, s)).

Definition put (x : s) : State unit := mkState (fun s => (tt, x)).

Definition modify f : State unit := mkState (fun s => (tt, f s)).

End State.

Arguments get [s].
Arguments gets [s a] f.
Arguments put [s] x.
Arguments modify [s] f.
