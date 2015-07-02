Require Import Hask.Ssr.
Require Import Hask.Ltac.
Require Import Hask.Data.Functor.

Generalizable All Variables.

Class Contravariant (f : Type -> Type) := {
  contramap : forall {a b : Type}, (a -> b) -> f b -> f a
}.

Arguments contramap {f _ a b} _ x.

Infix ">$<" := contramap (at level 28, left associativity, only parsing).
Notation "x >&< f" :=
  (contramap f x) (at level 28, left associativity, only parsing).

Notation "contramap[ M ]  f" := (@contramap M _ _ _ f) (at level 28).
Notation "contramap[ M N ]  f" :=
  (@contramap (fun X => M (N X)) _ _ _ f) (at level 26).
Notation "contramap[ M N O ]  f" :=
  (@contramap (fun X => M (N (O X))) _ _ _ f) (at level 24).

Definition coerce `{Functor f} `{Contravariant f} {a b} : f a -> f b :=
  fmap (False_rect _) \o contramap (False_rect _).

Instance Contravariant_Compose `{Functor F} `{Contravariant G} :
  Contravariant (F \o G) :=
{ contramap := fun A B => @fmap F _ (G B) (G A) \o @contramap G _ A B
}.

Module ContravariantLaws.

Include FunctorLaws.

Require Import FunctionalExtensionality.

Class ContravariantLaws (f : Type -> Type) `{Contravariant f} := {
  contramap_id   : forall a : Type, contramap (@id a) =1 id;
  contramap_comp : forall (a b c : Type) (f : b -> c) (g : a -> b),
    contramap g \o contramap f =1 contramap (f \o g)
}.

Corollary contramap_id_x `{ContravariantLaws f} :
  forall (a : Type) x, contramap (@id a) x = x.
Proof. exact: contramap_id. Qed.

Corollary contramap_id_ext `{ContravariantLaws f} :
  forall (a : Type), contramap (@id a) = id.
Proof.
  move=> a.
  extensionality x.
  exact: contramap_id.
Qed.

Corollary contramap_comp_x `{ContravariantLaws F} :
  forall (a b c : Type) (f : b -> c) (g : a -> b) x,
  contramap g (contramap f x) = contramap (fun y => f (g y)) x.
Proof. exact: contramap_comp. Qed.

Corollary contramap_comp_ext `{ContravariantLaws F} :
  forall (a b c : Type) (f : b -> c) (g : a -> b),
  contramap g \o contramap f = contramap (f \o g).
Proof.
  move=> a b c f g.
  extensionality x.
  exact: contramap_comp.
Qed.

Corollary contramap_compose  `{Functor F} `{Contravariant G} :
  forall {X Y} (f : X -> Y),
    @fmap F _ (G Y) (G X) (@contramap G _ X Y f) =
    @contramap (F \o G) _ X Y f.
Proof. by []. Qed.

Program Instance ContravariantLaws_Compose
  `{FunctorLaws F} `{ContravariantLaws G} : ContravariantLaws (F \o G).
Obligation 1. (* contramap_id *)
  move=> x.
  by rewrite contramap_id_ext fmap_id.
Qed.
Obligation 2. (* contramap_comp *)
  move=> x.
  rewrite fmap_comp.
  f_equal.
  extensionality y.
  by rewrite contramap_comp.
Qed.

End ContravariantLaws.
