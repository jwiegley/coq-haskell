Require Export Hask.Data.Semigroup.
Require Import Hask.Prelude.
Require Import Coq.Classes.Equivalence.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Monoid (m : Type) `{Equivalence m} := {
  is_semigroup :> Semigroup m;

  mempty : m;

  mempty_left  : forall a, mappend mempty a ≈ a;
  mempty_right : forall a, mappend a mempty ≈ a;
}.

Program Instance Monoid_option `{Monoid a} : Monoid (option a) := {
  mempty := None
}.
Next Obligation. reflexivity. Qed.
Next Obligation. destruct a0; reflexivity. Qed.
