Require Import Hask.Prelude.
Require Import Hask.Control.Monad.
Require Import Hask.Data.Functor.Contravariant.
Require Import Hask.Data.Functor.Identity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition Lens s t a b := forall `{Functor f}, (a -> f b) -> s -> f t.
Definition Lens' s a := Lens s s a a.

Definition Getter s a :=
  forall `{Functor f} `{Contravariant f}, (a -> f a) -> s -> f s.

Definition Getting r s a := (a -> Const r a) -> s -> Const r s.

Notation "x &+ f" := (f x) (at level 41, only parsing).

Definition set `(l : Lens s t a b) (x : b) : s -> t :=
  runIdentityF \o l _ _ (fun _ => Id _ x).
Notation "l .~ x" := (set l x) (at level 40).

Definition over `(l : Lens s t a b) (f : a -> b) : s -> t :=
  runIdentityF \o l _ _ (fun x => Id _ (f x)).
Notation "l %~ f" := (over l f) (at level 40).

Definition view `(f : Getting a s a) : s -> a := f id.
Notation "x ^_ l" := (view l x) (at level 40).

Definition stepdownl' `(l : Lens' s a) : Getting a s a := l _ _.
Coercion stepdownl' : Lens' >-> Getting.

Definition stepdowng `(l : Getter s a) : Getting a s a := l _ _ _.
Coercion stepdowng : Getter >-> Getting.

Notation "f \o+ g" := (fun x y => f x y \o g x y) (at level 41, only parsing).

Definition _1 {a b : Type} : Lens' (a * b) a :=
  fun _ _ f s => match s with (x, y) => fmap (fun z => (z, y)) (f x) end.
Definition _2 {a b : Type} : Lens' (a * b) b :=
  fun _ _ f s => match s with (x, y) => fmap (fun z => (x, z)) (f y) end.

Definition _ex1 {a : Type} {P : a -> Prop} : Getter { x : a | P x } a :=
  fun _ _ _ f s => fmap (const s) (f (proj1_sig s)).

Require Import Hask.Control.Monad.Trans.State.

Definition use `(l : Getting a s a) `{Monad m} : StateT s m a :=
  view l <$> getT.

Definition plusStateT `(l : Lens' s nat) (n : nat) `{Monad m} :
  StateT s m unit := modifyT (l %~ plus n).

Notation "l += n" := (plusStateT l n) (at level 41).

Definition modifyStateT `(l : Lens' s a) (x : a) `{Monad m} :
  StateT s m unit := modifyT (l .~ x).

Notation "l .= x" := (modifyStateT l x) (at level 41).

Definition applyStateT `(l : Lens' s a) (f : a -> a) `{Monad m} :
  StateT s m unit := modifyT (l %~ f).

Notation "l %= f" := (applyStateT l f) (at level 41).

Module LensLaws.

Class LensLaws `(l : Lens' s a) := {
  lens_view_set : forall (x : s) (y : a), view l (set l y x) = y;
  lens_set_view : forall (x : s), set l (view l x) x = x;
  lens_set_set  : forall (x : s) (y z : a), set l z (set l y x) = set l z x
}.

Program Instance Lens__1 {a b} : LensLaws (s:=a * b) _1.
Program Instance Lens__2 {a b} : LensLaws (s:=a * b) _2.

Example lens_ex1 : view _1 (10, 20) = 10.
Proof. reflexivity. Qed.

Example lens_ex2 : view _2 (10, 20) = 20.
Proof. reflexivity. Qed.

Example lens_ex3 : (10, 20) ^_ _2 = 20.
Proof. reflexivity. Qed.

Example lens_ex4 : (1, (2, (3, 4))) ^_ stepdownl' (_2 \o+ _2 \o+ _2) = 4.
Proof. reflexivity. Qed.

Example lens_ex5 : ((10, 20) &+ _1 .~ 500) = (500, 20).
Proof. reflexivity. Qed.

Example lens_ex6 : ((10, 20) &+ _1 %~ plus 1) = (11, 20).
Proof. reflexivity. Qed.

End LensLaws.
