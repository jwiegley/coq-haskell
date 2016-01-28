Require Import Hask.Prelude.
Require Import Hask.Control.Monad.

Generalizable All Variables.

(* Identity, in two flavors. *)

Definition Identity (a : Type) := a.

Program Instance Identity_Functor : Functor Identity := {
  fmap := fun _ _ => id
}.

Program Instance Identity_Applicative : Applicative Identity := {
  pure := fun _ => id;
  ap := fun _ _ => id
}.

Program Instance Identity_Monad : Monad Identity := {
  join := fun _ => id
}.

Inductive IdentityF (a : Type) := Id : a -> IdentityF a.

Definition runIdentityF `(x : IdentityF a) : a :=
  match x with Id y => y end.

Program Instance IdentityF_Functor : Functor IdentityF := {
  fmap := fun _ _ f x => Id _ (f (runIdentityF x))
}.

Program Instance IdentityF_Applicative : Applicative IdentityF := {
  pure := fun _ => Id _;
  ap := fun _ _ f x => Id _ (runIdentityF f (runIdentityF x))
}.

Program Instance IdentityF_Monad : Monad IdentityF := {
  join := fun _ => runIdentityF
}.
