Require Import Hask.Ltac.
Require Import Hask.Data.Functor.

Generalizable All Variables.

(* Left and Right Kan extensions *)

Definition Lan (f g : Type -> Type) (a : Type) :=
  { e : Type & ((f e -> a) * g e)%type }.

Definition Ran (f g : Type -> Type) (a : Type) :=
  forall r, (a -> f r) -> g r.

Axiom Ran_parametricity :
  forall `{Functor f} `{Functor g}
         a b c (k : Ran f g a) (g : b -> c) (h : a -> f b),
    fmap g (k _ h) = k _ (fmap g \o h).
