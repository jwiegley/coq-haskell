Require Import Hask.Data.Functor.
Require Import Hask.Data.Functor.Contravariant.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition Const (c a : Type) := c.

Program Instance Const_Functor (c : Type) : Functor (Const c) := {
  fmap := fun _ _ _ => id
}.

Program Instance Const_Contravariant (c : Type) : Contravariant (Const c) := {
  contramap := fun _ _ _ => id
}.
