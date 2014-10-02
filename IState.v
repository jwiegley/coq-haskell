Require Import IEndo.
Require Import IApplicative.
Require Import IMonad.

Generalizable All Variables.

Inductive IState (i o a : Type) := mkIState : (i -> (a * o)) -> IState i o a.

Arguments mkIState [i o a] _.

Definition runIState {i o a} (x : IState i o a) :=
  match x with mkIState f => f end.

Global Program Instance IState_IFunctor : IFunctor IState := {
    imap := fun _ _ _ _ f x =>
      mkIState (fun st => let (a,st') := runIState x st in (f a, st'))
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

Definition iget  {s}     : IState s s s := mkIState (fun i => (i, i)).
Definition igets {s a} f : IState s s a := mkIState (fun s => (f s, s)).

Definition iput {s} (x : s) : IState s s unit := mkIState (fun s => (tt, x)).

Definition imodify {i o} (f : i -> o) : IState i o unit :=
  mkIState (fun i => (tt, f i)).

Program Instance IState_IApplicative : IApplicative IState := {
    ipure := fun _ _ x => mkIState (fun st => (x, st));
    iap := fun _ _ _ _ _ f x =>
      mkIState (fun st =>
        let (f', st') := runIState f st in
        let (x', st'') := runIState x st' in
        (f' x', st''))
}.

Program Instance IState_IMonad : IMonad IState := {
    ijoin := fun _ _ _ _ x => mkIState (fun st =>
      let (y, st') := runIState x st in
      let (a, st'') := runIState y st' in
      (a, st''))
}.
Obligation 1.
  extensionality x.
  unfold compose.
  f_equal.
  extensionality y.
  destruct x. simpl.
  destruct (p y).
  destruct i. simpl.
  destruct (p0 j).
  destruct i. simpl.
  destruct (p1 k).
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
  destruct i. simpl.
  destruct (p0 a).
  reflexivity.
Qed.
