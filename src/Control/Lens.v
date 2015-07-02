Require Import Hask.Prelude.
Require Import Hask.Control.Monad.
Require Import Hask.Data.Functor.Identity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Definition Lens s t a b := forall `{Functor f}, (a -> f b) -> s -> f t.
Definition Lens' s a := Lens s s a a.

Notation "x &+ f" := (f x) (at level 71, only parsing).
Notation "f \o+ g" := (fun t h => f t h \o g t h) (at level 71, only parsing).

Definition set `(l : Lens s t a b) (x : b) : s -> t :=
  l _ _ (fun _ => x).
Notation "l .~ x" := (set l x) (at level 70).

Definition over `(l : Lens s t a b) (x : a -> b) : s -> t := l _ _ x.
Notation "l %~ f" := (over l f) (at level 70).

Definition view `(f : Lens' s a) : s -> a := f _ _ id.
Notation "x ^_ l" := (view l x) (at level 70).

Definition _1 {a b : Type} : Lens' (a * b) a := fun _ _ f s =>
  let: (x, y) := s in fmap (fun z => (z, y)) (f x).
Definition _2 {a b : Type} : Lens' (a * b) b := fun _ _ f s =>
  let: (x, y) := s in fmap (fun z => (x, z)) (f y).

Class CorrectLens `(l : Lens' s a) := {
  lens_view_set : forall (x : s) (y : a), view l (set l y x) = y;
  lens_set_view : forall (x : s), set l (view l x) x = x;
  lens_set_set  : forall (x : s) (y z : a), set l z (set l y x) = set l z x
}.

Program Instance Lens__1 : CorrectLens (s:=a * b) _1.
Program Instance Lens__2 : CorrectLens (s:=a * b) _2.

Example lens_ex1 : view _1 (10, 20) == 10.
Proof. reflexivity. Qed.

Example lens_ex2 : view _2 (10, 20) == 20.
Proof. reflexivity. Qed.

Example lens_ex3 : (10, 20) ^_ _2 == 20.
Proof. reflexivity. Qed.

Example lens_ex4 : (1, (2, (3, 4))) ^_ (_2 \o+ _2 \o+ _2) == 4.
Proof. reflexivity. Qed.

Example lens_ex5 : ((10, 20) &+ _1 .~ 500) == (500, 20).
Proof. reflexivity. Qed.

Example lens_ex6 : ((10, 20) &+ _1 %~ plus 1) == (11, 20).
Proof. reflexivity. Qed.
