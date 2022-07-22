Require Import Hask.Ltac.
Require Import Hask.Data.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Contravariant (f : Type -> Type) := {
  contramap : forall {a b : Type}, (a -> b) -> f b -> f a
}.

Arguments contramap {f _ a b} _ x.

Infix ">$<" := contramap (at level 28, left associativity, only parsing).
Notation "x >&< f" :=
  (contramap f x) (at level 28, left associativity, only parsing).

Notation "contramap[ M ]  f" := (@contramap M _ _ _ f) (at level 9).
Notation "contramap[ M N ]  f" :=
  (@contramap (fun X => M (N X)) _ _ _ f) (at level 9).
Notation "contramap[ M N O ]  f" :=
  (@contramap (fun X => M (N (O X))) _ _ _ f) (at level 9).

Definition coerce `{Functor f} `{Contravariant f} {a b} : f a -> f b :=
  fmap (False_rect _) \o contramap (False_rect _).

#[export]
Instance Contravariant_Compose `{Functor F} `{Contravariant G} :
  Contravariant (F \o G) :=
{ contramap := fun A B => @fmap F _ (G B) (G A) \o @contramap G _ A B
}.

Require Import FunctionalExtensionality.

Module ContravariantLaws.

Include FunctorLaws.

Class ContravariantLaws (f : Type -> Type) `{Contravariant f} := {
  contramap_id   : forall a : Type, contramap (@id a) = id;
  contramap_comp : forall (a b c : Type) (f : b -> c) (g : a -> b),
    contramap g \o contramap f = contramap (f \o g)
}.

Corollary contramap_id_x `{ContravariantLaws f} :
  forall (a : Type) x, contramap (@id a) x = x.
Proof. intros; rewrite contramap_id. auto. Qed.

Corollary contramap_comp_x `{ContravariantLaws F} :
  forall (a b c : Type) (f : b -> c) (g : a -> b) x,
  contramap g (contramap f x) = contramap (fun y => f (g y)) x.
Proof.
  intros.
  replace (fun y : a => f (g y)) with (f \o g).
    rewrite <- contramap_comp.
    reflexivity.
  reflexivity.
Qed.

Corollary contramap_compose  `{Functor F} `{Contravariant G} :
  forall {X Y} (f : X -> Y),
    @fmap F _ (G Y) (G X) (@contramap G _ X Y f) =
    @contramap (F \o G) _ X Y f.
Proof. reflexivity. Qed.

#[export]
Program Instance ContravariantLaws_Compose
  `{FunctorLaws F} `{ContravariantLaws G} : ContravariantLaws (F \o G).
Obligation 1. (* contramap_id *)
  extensionality x.
  rewrite contramap_id, fmap_id.
  reflexivity.
Qed.
Obligation 2. (* contramap_comp *)
  extensionality x.
  rewrite fmap_comp, contramap_comp.
  reflexivity.
Qed.

End ContravariantLaws.
