Require Import Endo.
Require Import Applicative.
Require Import Monad.
Require Import Coq.Classes.RelationClasses.

Generalizable All Variables.

Close Scope nat_scope.

Section RState.

Variables s n : Type.
Variables fs : s -> n.
Hypothesis P : relation n.
Context `{PreOrder _ P}.

Inductive RState (a : Type) :=
  mkRState : (forall i : s, (a * { o : s | P (fs i) (fs o) })) -> RState a.

Definition runRState {a} (x : RState a) := match x with mkRState f => f end.

End RState.

Arguments mkRState [s n fs P a] _.
Arguments runRState [s n fs P a] _ i.

Definition rget {s n fs} {P : relation n} `{PreOrder _ P}
  : RState s n fs P s :=
  mkRState (fun i =>
    (i, exist (fun o : s => P (fs i) (fs o)) i (reflexivity (fs i)))).

Definition rgets {s n fs a} {P : relation n} `{PreOrder _ P} f
  : RState s n fs P a :=
  mkRState (fun i => let z := fs i in
    (f i, exist (fun o : s => P z (fs o)) i (reflexivity z))).

Definition rmodify {s n fs} {P : relation n} `{PreOrder _ P} (f : s -> s)
  (H : forall (i o : s), P (fs i) (fs o)) : RState s n fs P unit :=
  mkRState (fun i => let z := f i in
    (tt, exist (fun o : s => P (fs i) (fs o)) z (H i z))).

Definition rtype {s n : Type} (fs : s -> n) (P : relation n)
  `{PreOrder _ P} := RState s n fs P.

Program Instance RState_Functor {s n : Type} {fs : s -> n}
  {P : relation n} `{PreOrder _ P} : Functor (rtype fs P) := {
    fmap := fun _ _ f x =>
      mkRState (fun st => let (a,st') := runRState x st in (f a, st'))
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

Program Instance RState_Applicative {s n : Type} {fs : s -> n}
  {P : relation n} `{PreOrder _ P} : Applicative (rtype fs P) := {
    pure := fun _ x => mkRState (fun st => (x, st));
    ap := fun _ _ f x =>
      mkRState (fun st =>
        let (f', st') := runRState f st in
        let (x', st'') := runRState x st' in
        (f' x', st''))
}.
Obligation 1. reflexivity. Defined.
Obligation 2. transitivity (fs st'); assumption. Defined.
Obligation 3.
  extensionality x.
  destruct x. compute.
  f_equal.
  extensionality st.
  destruct (p st).
  f_equal. destruct s0.
  f_equal. apply proof_irrelevance.
Qed.
Obligation 4.
  f_equal.
  extensionality st.
  destruct u. simpl.
  destruct (p st).
  destruct v. simpl.
  destruct (p0 (proj1_sig s0)).
  destruct w. simpl.
  destruct (p1 (proj1_sig s1)).
  f_equal. f_equal.
  compute. apply proof_irrelevance.
Qed.
Obligation 5.
  f_equal.
  extensionality st.
  f_equal.
  f_equal. apply proof_irrelevance.
Qed.
Obligation 6.
  f_equal.
  extensionality st.
  destruct u. simpl.
  destruct (p st).
  f_equal. f_equal.
  compute. apply proof_irrelevance.
Qed.
Obligation 7.
  extensionality x.
  f_equal.
  extensionality st.
  destruct x. simpl.
  destruct (p st).
  f_equal.
  destruct s0. f_equal.
  compute. apply proof_irrelevance.
Qed.

Program Instance RState_Monad {s n : Type} {fs : s -> n}
  {P : relation n} `{PreOrder _ P} : Monad (rtype fs P) := {
    join := fun _ x => mkRState (fun st =>
      let (y, st') := runRState x st in
      let (a, st'') := runRState y st' in
      (a, st''))
}.
Obligation 1. transitivity (fs st'); assumption. Defined.
Obligation 2.
  extensionality x.
  unfold compose.
  f_equal.
  extensionality st.
  destruct x. simpl.
  destruct (p st).
  destruct r. simpl.
  destruct (p0 (proj1_sig s0)).
  destruct r. simpl.
  destruct (p1 (proj1_sig s1)).
  f_equal. f_equal.
  compute.
  destruct s0.
  destruct s1.
  destruct s2.
  apply proof_irrelevance.
Qed.
Obligation 3.
  extensionality x.
  unfold compose, id.
  destruct x.
  f_equal. simpl.
  extensionality y.
  destruct (p y). simpl.
  f_equal.
  destruct s0. f_equal.
  apply proof_irrelevance.
Qed.
Obligation 4.
  extensionality x.
  unfold compose, id.
  destruct x. simpl.
  f_equal.
  extensionality y.
  destruct (p y).
  f_equal.
  destruct s0. f_equal.
  compute.
  apply proof_irrelevance.
Qed.
Obligation 5.
  extensionality x.
  unfold compose.
  f_equal.
  extensionality y.
  destruct x. simpl.
  destruct (p y). simpl.
  destruct r. simpl.
  destruct (p0 (proj1_sig s0)).
  f_equal.
Qed.
