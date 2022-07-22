Require Import Hask.Ltac.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Functor (f : Type -> Type) : Type := {
  fmap : forall {a b : Type}, (a -> b) -> f a -> f b
}.

Arguments fmap {f _ a b} g x.

Infix "<$>" := fmap (at level 28, left associativity, only parsing).
Infix "<$[ M ]>" :=
  (@fmap M _ _ _) (at level 28, left associativity, only parsing).
Notation "x <$ m" :=
  (fmap (const x) m) (at level 28, left associativity, only parsing).
Notation "x <&> f" :=
  (fmap f x) (at level 28, left associativity, only parsing).

Notation "fmap[ M ]" := (@fmap M _ _ _) (at level 9).
Notation "fmap[ M N ]" := (@fmap (fun X => M (N X)) _ _ _) (at level 9).
Notation "fmap[ M N O ]" :=
  (@fmap (fun X => M (N (O X))) _ _ _) (at level 9).

Require Import FunctionalExtensionality.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

Module FunctorLaws.

(* Functors preserve extensional equality for the applied function.
   This is needed to perform setoid rewriting within the function
   passed to a functor. *)
Add Parametric Morphism {A B} `{Functor F} : (@fmap F _ A B)
  with signature (pointwise_relation _ eq ==> eq ==> eq)
    as mul_isomorphism.
Proof.
  intros.
  f_equal.
  extensionality e.
  apply H0.
Qed.

Class FunctorLaws (f : Type -> Type) `{Functor f} := {
  fmap_id   : forall a : Type, fmap (@id a) = id;
  fmap_comp : forall (a b c : Type) (f : b -> c) (g : a -> b),
    fmap f \o fmap g = fmap (f \o g)
}.

Corollary fmap_id_x `{FunctorLaws f} : forall (a : Type) x, fmap (@id a) x = x.
Proof.
  intros.
  rewrite fmap_id.
  reflexivity.
Qed.

Corollary fmap_comp_x `{FunctorLaws F} :
  forall (a b c : Type) (f : b -> c) (g : a -> b) x,
  fmap f (fmap g x) = fmap (fun y => f (g y)) x.
Proof.
  intros.
  replace (fun y : a => f (g y)) with (f \o g).
    rewrite <- fmap_comp.
    reflexivity.
  reflexivity.
Qed.

End FunctorLaws.
