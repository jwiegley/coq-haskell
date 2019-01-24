Require Import Hask.Ltac.
Require Import Hask.Data.Functor.
Require Import Hask.Data.Functor.Contravariant.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Left and Right Kan extensions *)

Definition Lan (f g : Type -> Type) (a : Type) :=
  { e : Type & ((f e -> a) * g e)%type }.

(* As with any data structure, we can provide its final encoding. *)
Definition Lan_final (f g : Type -> Type) (a : Type) :=
  forall r, (forall x : Type, (f x -> a) -> g x -> r) -> r.

Axiom Lan_final_parametricity :
  forall a b c f g
         (k : Lan_final f g a)
         (h : forall x : Type, (f x -> a) -> g x -> b)
         (x : b -> c),
    x (k b h) = k c (fun e n z => x (h e n z)).

Definition Ran (f g : Type -> Type) (a : Type) :=
  forall r, (a -> f r) -> g r.

Axiom Ran_parametricity :
  forall a b c `{Functor f} `{Functor g}
         (k : Ran f g a) (g : b -> c) (h : a -> f b),
    fmap g (k _ h) = k _ (fmap g \o h).
