Require Import Hask.Ssr.

Generalizable All Variables.

Class Functor (f : Type -> Type) := {
  fmap : forall {a b : Type}, (a -> b) -> f a -> f b
}.

Arguments fmap {f _ a b} _ x.

Notation "f <$> x" :=
  (fmap f x) (at level 28, left associativity, only parsing).
Notation "x <&> f" :=
  (fmap f x) (at level 28, left associativity, only parsing).

Program Instance Functor_Compose `{Functor F} `{Functor G} : Functor (F \o G) :=
{ fmap := fun A B => @fmap F _ (G A) (G B) \o @fmap G _ A B
}.

Module FunctorLaws.

Require Import FunctionalExtensionality.

Class FunctorLaws (f : Type -> Type) `{Functor f} := {
  fmap_id   : forall a : Type, fmap (@id a) =1 id;
  fmap_comp : forall (a b c : Type) (f : b -> c) (g : a -> b),
    fmap f \o fmap g =1 fmap (f \o g)
}.

Corollary fmap_id_x `{FunctorLaws f} : forall (a : Type) x, fmap (@id a) x = x.
Proof. exact: fmap_id. Qed.

Corollary fmap_id_ext `{FunctorLaws f} : forall (a : Type), fmap (@id a) = id.
Proof.
  move=> a.
  extensionality x.
  exact: fmap_id.
Qed.

Corollary fmap_comp_x `{FunctorLaws F} :
  forall (a b c : Type) (f : b -> c) (g : a -> b) x,
  fmap f (fmap g x) = fmap (fun y => f (g y)) x.
Proof. exact: fmap_comp. Qed.

Corollary fmap_comp_ext `{FunctorLaws F} :
  forall (a b c : Type) (f : b -> c) (g : a -> b),
  fmap f \o fmap g = fmap (f \o g).
Proof.
  move=> a b c f g.
  extensionality x.
  exact: fmap_comp.
Qed.

Ltac recomp :=
  repeat match goal with
    | [ |- ?F (?G ?X) = _ ] =>
        replace (F (G X)) with ((F \o G) X); last by rewrite /funcomp
    | [ |- _ = ?F (?G ?X) ] =>
        replace (F (G X)) with ((F \o G) X); last by rewrite /funcomp
    end.

Corollary fmap_compose  `{Functor F} `{Functor G} : forall {X Y} (f : X -> Y),
  @fmap F _ (G X) (G Y) (@fmap G _ X Y f) = @fmap (F \o G) _ X Y f.
Proof. by []. Qed.

Program Instance Functor_Compose `{FunctorLaws F} `{FunctorLaws G} :
  FunctorLaws (F \o G).
Obligation 1. (* fmap_id *)
  move=> x.
  by rewrite fmap_id_ext fmap_id.
Qed.
Obligation 2. (* fmap_comp *)
  move=> x.
  rewrite fmap_comp.
  f_equal.
  extensionality y.
  by rewrite fmap_comp.
Qed.

End FunctorLaws.
