Require Import Hask.Prelude.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Semigroup (m : Type) `{Equivalence m} := {
  mappend : m -> m -> m;

  mappend_respects :> Proper (equiv ==> equiv ==> equiv) mappend;

  mappend_assoc : forall a b c, mappend a (mappend b c) ≈ mappend (mappend a b) c;
}.

Arguments mappend {m _ _ _} _ _.

Infix "⨂" := mappend (at level 40).

Definition Maybe_append `{Semigroup a} (x y : Maybe a) : Maybe a :=
  match x, y with
  | Nothing, x     => x
  | x, Nothing     => x
  | Just x, Just y => Just (x ⨂ y)
  end.

Lemma Just_Proper `{Semigroup a} :
  Proper (equiv ==> equiv) Just.
Proof.
  repeat intro.
  apply H1.
Qed.

Lemma Maybe_append_Proper `{Semigroup a} :
  Proper (equiv ==> equiv ==> equiv) Maybe_append.
Proof.
  repeat intro.
  destruct x, x0, y, y0;
  simpl; auto;
  try contradiction.
  apply mappend_respects;
  first [ apply H1 | apply H2 ].
Qed.

Program Instance Semigroup_Maybe `{Semigroup a} : Semigroup (Maybe a) := {
  mappend := Maybe_append;
  mappend_respects := Maybe_append_Proper
}.
Next Obligation.
  destruct a0, b, c; simpl; try reflexivity.
  now apply mappend_assoc.
Qed.
