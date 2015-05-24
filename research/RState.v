Require Import Endo.
Require Import Applicative.
Require Import Monad.
Require Import Coq.Classes.RelationClasses.

Generalizable All Variables.

Close Scope nat_scope.

Definition proj1_sigg {A} {P Q : A -> Prop} (e : {x : A | P x & Q x}) : A :=
  let (x,_,_) := e in x.

Definition proj2_sigg {A} {P Q : A -> Prop} (e : {x : A | P x & Q x})
  : P (proj1_sigg e) := let (x,p,_) as x return (P (proj1_sigg x)) := e in p.

Definition proj3_sigg {A} {P Q : A -> Prop} (e : {x : A | P x & Q x})
  : Q (proj1_sigg e) := let (x,_,q) as x return (Q (proj1_sigg x)) := e in q.

Section RState.

Variables s n : Type.
Variables fs : s -> n.
Hypotheses P Q : relation n.
Context `{PreOrder _ P}.

Inductive RState (a : Type) :=
  mkRState :
    (forall (i : s) (H : { pre : s | P (fs pre) (fs i) & Q (fs pre) (fs i) }),
      (a * { o : s | P (fs i) (fs o) & Q (fs (proj1_sigg H)) (fs o) }))
    -> RState a.

Definition runRState {a} (x : RState a) := match x with mkRState f => f end.

End RState.

Arguments mkRState [s n fs P Q a] _.
Arguments runRState [s n fs P Q a] _ i H.

Definition rget {s n fs} {P Q : relation n} `{PreOrder _ P}
  : RState s n fs P Q s.
Proof.
  constructor. intros.
  split. apply i.
  destruct H0.
  exists i. reflexivity.
  assumption.
Defined.

Definition rgets {s n fs a} {P Q : relation n} `{PreOrder _ P} (f : s -> a)
  : RState s n fs P Q a.
Proof.
  constructor. intros.
  split. apply (f i).
  destruct H0.
  exists i. reflexivity.
  assumption.
Defined.

Definition rmodify {s n fs} {P Q : relation n} `{PreOrder _ P}
  (f : forall (i : s)
              (H : { pre : s | P (fs pre) (fs i) & Q (fs pre) (fs i) }),
         { o : s | P (fs i) (fs o) & Q (fs (proj1_sigg H)) (fs o) })
  : RState s n fs P Q unit.
Proof.
  constructor. intros.
  split. apply tt.
  specialize (f i H0).
  destruct f.
  exists x; assumption.
Defined.

Definition rtype {s n : Type} (fs : s -> n) (P Q : relation n)
  `{PreOrder _ P} := RState s n fs P Q.

Program Instance RState_Functor {s n : Type} {fs : s -> n}
  {P Q : relation n} `{PreOrder _ P} : Functor (rtype fs P Q) := {
    fmap := fun _ _ f x =>
      mkRState (fun st H => let (a,st') := runRState x st H in (f a, st'))
}.
Obligation 1.
  extensionality x.
  destruct x.
  unfold id.
  f_equal.
  extensionality st.
  simpl.
  extensionality H0.
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
  extensionality H0.
  destruct (p y).
  reflexivity.
Qed.

Program Instance RState_Applicative {s n : Type} {fs : s -> n}
  {P Q : relation n} `{PreOrder _ P} : Applicative (rtype fs P Q).
Obligation 1.
  constructor. intros i H0.
  split. apply X0.
  destruct H0.
  exists i. reflexivity.
  assumption.
Defined.
Obligation 2.
  rename X0 into mf.
  rename X1 into mx.
  constructor. intros st ev.
  destruct mf as [mf].
  specialize (mf st ev).
  destruct ev as [pre HP HQ].
  destruct mf as [f [st' HP' HQ']].
  destruct mx as [mx].
  assert (P (fs pre) (fs st')) as HP''.
    transitivity (fs st); assumption.
  assert (Q (fs pre) (fs st')) as HQ''. assumption.
  specialize (mx st'
    (exist2 (fun o => P (fs o) (fs st'))
            (fun o => Q (fs o) (fs st')) pre HP'' HQ'')).
  destruct mx as [x [st'' HP''' HQ''']].
  split. apply (f x).
  exists st''.
  transitivity (fs st'); assumption.
  assumption.
Defined.
Obligation 3.
  extensionality x.
  destruct x. compute.
  f_equal.
  extensionality st.
  extensionality ev.
  destruct (p st ev).
  destruct s0.
Admitted.
Obligation 4.
  compute.
  f_equal.
  extensionality st.
  extensionality ev.
  destruct u. simpl.
  destruct (p st ev).
  destruct ev as [pre HP HQ].
  destruct v. simpl in *.

  destruct s0 as [st' HP' HQ'].
  assert (P (fs pre) (fs st')) as HP''.
    transitivity (fs st); assumption.
  assert (Q (fs pre) (fs st')) as HQ''. assumption.
  destruct (p0 st'
    (exist2 (fun o => P (fs o) (fs st'))
            (fun o => Q (fs o) (fs st')) pre HP'' HQ'')).
  simpl in *.

  destruct s0 as [st'' HP''' HQ'''].
  assert (P (fs pre) (fs st'')) as HP''''.
    transitivity (fs st'); assumption.
  assert (Q (fs pre) (fs st'')) as HQ''''. assumption.
  destruct (p0 st''
    (exist2 (fun o => P (fs o) (fs st''))
            (fun o => Q (fs o) (fs st'')) pre HP'''' HQ'''')).
  simpl in *.
Admitted.
Obligation 5.
  compute. f_equal.
  extensionality st.
  extensionality ev.
  destruct ev.
  f_equal. f_equal.
  apply proof_irrelevance.
Qed.
Obligation 6.
  compute. f_equal.
  extensionality st.
  extensionality ev.
  destruct u. simpl.
  destruct (p st ev).
  destruct s0 as [st' HP' HQ'].
Admitted.
Obligation 7.
  compute.
  extensionality x.
  f_equal.
  extensionality st.
  extensionality ev.
  destruct x.
  destruct ev as [pre HP HQ].
  destruct (p st (exist2 (fun o => P (fs o) (fs st))
                         (fun o => Q (fs o) (fs st)) pre HP HQ)).
  destruct s0. simpl in *.
Admitted.

Program Instance RState_Monad {s n : Type} {fs : s -> n}
  {P Q : relation n} `{PreOrder _ P} : Monad (rtype fs P Q).
Obligation 1.
  rename X0 into x.
  constructor. intros st ev.
  destruct x.
  destruct (p st ev) as [y [st' HP' HQ']].
  destruct y as [y].

  destruct ev as [pre HP HQ].
  assert (P (fs pre) (fs st')) as HP''.
    transitivity (fs st); assumption.
  assert (Q (fs pre) (fs st')) as HQ''. assumption.

  destruct (y st'
    (exist2 (fun o => P (fs o) (fs st'))
            (fun o => Q (fs o) (fs st')) pre HP'' HQ''))
    as [a [st'' HP''' HQ''']].
  simpl in *.

  split. apply a.
  exists st''.
  transitivity (fs st'); assumption.
  assumption.
Defined.
Obligation 2.
  (* Set Printing All. *)
  extensionality r.
  destruct r.
  unfold RState_Monad_obligation_1, compose.
  f_equal.
  extensionality st.
  extensionality ev. simpl.
  destruct (p st ev).
  destruct r.
  destruct s0 as [st' HP' HQ'].
  destruct ev.
  destruct (p0 st').
  destruct r.
  destruct s0 as [st'' HP'' HQ''].
  simpl in *.
  replace (@transitivity n P (@PreOrder_Transitive n P H)
             (fs x) (fs st') (fs st'')
           (@transitivity n P (@PreOrder_Transitive n P H)
              (fs x) (fs st) (fs st') p1 HP') HP'')
     with (@transitivity n P (@PreOrder_Transitive n P H)
             (fs x) (fs st) (fs st'') p1
           (@transitivity n P (@PreOrder_Transitive n P H)
             (fs st) (fs st') (fs st'') HP' HP'')).
  destruct (p2 st'').
  destruct s0.
  f_equal. f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.
Obligation 3.
  compute.
  extensionality x.
  destruct x.
  f_equal.
  extensionality y.
  extensionality ev.
  destruct (p y ev).
  destruct ev.
  destruct s0.
  f_equal. f_equal.
  apply proof_irrelevance.
Qed.
Obligation 4.
  compute.
  extensionality x.
  destruct x. f_equal.
  extensionality st.
  extensionality ev.
  destruct ev.
  assert (forall z,
    ((let (_, PreOrder_Transitive) := H in PreOrder_Transitive)
     (fs x) (fs st) (fs st) z
     ((let (PreOrder_Reflexive, _) := H in PreOrder_Reflexive)
      (fs st))) = z).
    intros. apply proof_irrelevance. rewrite H0.
  destruct (p st).
  destruct s0.
  f_equal. f_equal. apply proof_irrelevance.
Qed.
Obligation 5.
  compute.
  extensionality x.
  destruct x. simpl.
  f_equal.
  extensionality y.
  extensionality ev.
  destruct (p y ev). simpl.
  destruct ev.
  destruct s0.
  destruct r. simpl.
  destruct (p2 x0). simpl in *.
  destruct s0. reflexivity.
Qed.
