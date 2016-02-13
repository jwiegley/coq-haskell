Definition Fix (f : Type -> Type) :=
  forall r, (forall x, (x -> r) -> f x -> r) -> r.
