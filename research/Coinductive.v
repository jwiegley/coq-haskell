Require Import Hask.Prelude.

Generalizable All Variables.

Module Type Bisimulation.

Variables T C : Type.
Variable embed : T -> C.
Variable approx : nat -> C -> T.

Hypothesis approx_embed : forall x : T, exists m : nat, approx m (embed x) = x.

Lemma embed_approx : forall n (c : C),
  approx n c = approx n (embed (approx n c)).
Proof.
  move=> n c.
  destruct (approx_embed (approx n c)).
  rewrite -{1}H.
  f_equal.

Theorem approximately : forall (c : C) (P : C -> Prop) (n : nat) (t : T),
  t = approx n c -> P (embed t) -> P c.
Proof.
  move=> c ? n t Heqe H.
  rewrite Heqe in H.
  rewrite embed_approx in H.
  have H0 := approx_embed t.
  destruct H0.
  rewrite Heqe -(approx_inj n c (embed _)) // in H.
  exact: embed_approx.
Qed.

End Bisimulation.

Module Streams <: Bisimulation.

CoInductive stream (a : Type) :=
  | SNil : stream a
  | SCons : a -> stream a -> stream a.

Variable a : Type.

Definition T := seq a.
Definition C := stream a.

CoFixpoint embed_stream `(x : seq a) : stream a :=
  match x with
    | nil => SNil _
    | cons x xs => SCons _ x (embed_stream xs)
  end.

Fixpoint approx_stream (n : nat) `(x : stream a) : seq a :=
  if n isn't S n' then nil else
  match x with
  | SNil => nil
  | SCons x xs => cons x (approx_stream n' xs)
  end.

Definition embed := embed_stream.
Definition approx := approx_stream.

Lemma approx_embed : forall x : T, exists m : nat, approx m (embed x) = x.

Lemma embed_approx : forall n (c : C),
  approx n c = approx n (embed (approx n c)).

End Streams.
