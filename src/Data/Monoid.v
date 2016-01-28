Require Import Hask.Control.Monad.

Generalizable All Variables.

Class Monoid (m : Type) := {
  mempty : m;
  mappend : m -> m -> m;

  mon_left_id  : forall a, mappend mempty a = a;
  mon_right_id : forall a, mappend a mempty = a;
  mon_assoc    : forall a b c, mappend a (mappend b c) = mappend (mappend a b) c
}.
