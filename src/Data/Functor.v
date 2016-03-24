Require Import Hask.Ltac.

Generalizable All Variables.

Class Functor (f : Type -> Type) : Type := {
  fmap : forall {a b : Type}, (a -> b) -> f a -> f b
}.

Arguments fmap {f _ a b} g x.

Infix "<$>" := fmap (at level 28, left associativity, only parsing).
Notation "x <&> f" :=
  (fmap f x) (at level 28, left associativity, only parsing).

Notation "fmap[ M ]" := (@fmap M _ _ _) (at level 9).
Notation "fmap[ M N ]" := (@fmap (fun X => M (N X)) _ _ _) (at level 9).
Notation "fmap[ M N O ]" :=
  (@fmap (fun X => M (N (O X))) _ _ _) (at level 9).

Instance Compose_Functor `{Functor F} `{Functor G} : Functor (F \o G) :=
{ fmap := fun A B => @fmap F _ (G A) (G B) \o @fmap G _ A B
}.

Instance Impl_Functor {A} : Functor (fun B => A -> B) := {
  fmap := fun A B f run => fun xs => f (run xs)
}.

Module FunctorLaws.

Require Import FunctionalExtensionality.

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

Corollary fmap_compose  `{Functor F} `{Functor G} : forall {X Y} (f : X -> Y),
  @fmap F _ (G X) (G Y) (@fmap G _ X Y f) = @fmap (F \o G) _ X Y f.
Proof. reflexivity. Qed.

Program Instance Compose_FunctorLaws `{FunctorLaws F} `{FunctorLaws G} :
  FunctorLaws (F \o G).
Obligation 1. (* fmap_id *)
  extensionality x.
  do 2 rewrite fmap_id.
  reflexivity.
Qed.
Obligation 2. (* fmap_comp *)
  extensionality x.
  do 2 rewrite fmap_comp.
  reflexivity.
Qed.

Program Instance Impl_FunctorLaws {A} : FunctorLaws (fun B => A -> B).

End FunctorLaws.
