Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition Fix (f : Type -> Type) :=
  forall r, (forall x, (x -> r) -> f x -> r) -> r.
