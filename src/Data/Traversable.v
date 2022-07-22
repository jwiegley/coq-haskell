Require Import
  Hask.Control.Monad
  Hask.Data.Maybe.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Traversable `{Functor t} := {
  sequence : forall `{Applicative f} a, t (f a) -> f (t a)

  (* naturality
       t . sequence = sequence . fmap t for every applicative transformation t
     identity
       sequence . fmap Identity = Identity
     composition
       sequence . fmap Compose = Compose . fmap sequence . sequence
  *)
}.

Arguments sequence {t H _ f _ a} _.

Arguments Traversable t [H].

(* Tupersable is a specialization of Traversable that applies only to tuples,
   and thus does not require that tuples be Applicative. *)

Class Tupersable {rep} `{Functor t} := {
  sequenceT : forall a, rep -> t (rep * a)%type -> rep * t a
}.

Arguments sequenceT {rep t H _ a} _ _.

Arguments Tupersable rep t [H].

#[export]
Instance Maybe_Traversable : Traversable Maybe := {
  sequence := fun _ _ A x =>
    match x with
    | Nothing => pure Nothing
    | Just x  => fmap Just x
    end
}.

#[export]
Instance Maybe_Tupersable {rep} : Tupersable rep Maybe := {
  sequenceT := fun A (s : rep) x =>
    match x with
    | Nothing => (s, Nothing)
    | Just (s', x)  => (s', Just x)
    end
}.
