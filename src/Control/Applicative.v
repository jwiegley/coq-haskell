Require Export Hask.Ltac.
Require Export Hask.Control.Category.
Require Export Hask.Data.Functor.

Generalizable All Variables.

Reserved Notation "f <*> g" (at level 28, left associativity).

Section Applicative.

(* Class Cartesian `{Category C} := { *)
(*   product : forall a b : C, C *)
(* }. *)
(* Arguments Cartesian {_ Arr} H. *)

Notation "x × y" := (x * y)%type (at level 30).

(* Class Closed `{Category C} := { *)
(*   exponent : forall a b : C, C *)
(* }. *)
(* Arguments Closed {_ Arr} H. *)

(* Class Monoidal `{Category C} := { *)
(*   tensor_product  : C × C ⟶ C; *)
(*   identity_object : C *)
(* }. *)

Context `{Category C}.

Inductive product (A B : Set) : Set :=  paired : A -> B -> product A B.

Set Printing All.
Print prod.
Check @Functor (product (C^op) C) _ _ Coq _ _.

Instance Hom_Functor : C^op × C ⟶ Coq.

Context `{Category D}.

Class Applicative := {
  is_functor :> C ⟶ D;

  pure : forall a : C, a -> fobj[is_functor] a;
  ap   : forall a b : C, fobj[is_functor] (a ~> b) ~> (fobj a ~> fobj b)
    where "f <*> g" := (ap f g)
}.

End Applicative.

Arguments pure {f _ _} _.
Arguments ap   {f _ _ _} _ x.

Notation "pure[ M ]" := (@pure M _ _) (at level 19, M at next level).
Notation "pure[ M N ]" := (@pure (fun X => M (N X)) _ _) (at level 9).

Notation "ap[ M ]" := (@ap M _ _ _) (at level 9).
Notation "ap[ M N ]" := (@ap (fun X => M (N X)) _ _ _) (at level 9).
Notation "ap[ M N O ]" := (@ap (fun X => M (N (O X))) _ _ _) (at level 9).

Infix "<*>" := ap (at level 28, left associativity).

(* Notation "[| f x y .. z |]" := (.. (f <$> x <*> y) .. <*> z) *)
(*     (at level 9, left associativity, f at level 9, *)
(*      x at level 9, y at level 9, z at level 9). *)

Definition liftA2 `{Applicative m} {A B C : Type}
  (f : A -> B -> C) (x : m A) (y : m B) : m C := ap (fmap f x) y.

Instance Compose_Applicative (F : Type -> Type) (G : Type -> Type)
  `{Applicative F} `{Applicative G} : Applicative (F \o G)  :=
{ is_functor := Compose_Functor (F:=F) (G:=G)
; pure := fun A   => @pure F _ (G A) \o @pure G _ A
; ap   := fun A B => ap \o fmap (@ap G _ A B)
}.

Instance Impl_Applicative {A} : Applicative (fun B => A -> B) := {
  pure := fun _ x => fun _ => x;
  ap   := fun _ _ runf runx => fun xs => runf xs (runx xs)
}.

Module ApplicativeLaws.

Include FunctorLaws.

Require Import FunctionalExtensionality.

Class ApplicativeLaws (f : Type -> Type) `{Applicative f} := {
  has_functor_laws :> FunctorLaws f;

  ap_id : forall a : Type, ap (pure (@id a)) = id;
  ap_comp : forall (a b c : Type) (v : f (a -> b)) (u : f (b -> c)) (w : f a),
    pure (fun f g x => f (g x)) <*> u <*> v <*> w = u <*> (v <*> w);
  ap_homo : forall (a b : Type) (x : a) (f : a -> b),
    pure f <*> pure x = pure (f x);
  ap_interchange : forall (a b : Type) (y : a) (u : f (a -> b)),
    u <*> pure y = pure (fun f => f y) <*> u;

  ap_fmap : forall (a b : Type) (f : a -> b),
    ap (pure f) = @fmap _ is_functor _ _ f
}.

Corollary fmap_pure `{ApplicativeLaws m} : forall (a b : Type) (f : a -> b),
  fmap[m] f \o pure = pure \o f.
Proof.
  intros a b f.
  extensionality x.
  unfold Basics.compose.
  rewrite <- ap_fmap.
  apply ap_homo.
Qed.

Corollary fmap_pure_x `{ApplicativeLaws m} : forall (a b : Type) (f : a -> b) x,
  fmap[m] f (pure x) = pure (f x).
Proof.
  intros.
  replace (pure[m] (f x)) with ((pure[m] \o f) x).
    rewrite <- fmap_pure.
    reflexivity.
  reflexivity.
Qed.

Ltac apply_applicative_laws :=
  repeat
    match goal with
    | [ |- context[fmap[?F] id] ] =>
      rewrite fmap_id
    | [ |- context[fmap[?F] _ (fmap[?F] _ _)] ] =>
      rewrite fmap_comp_x

    | [ |- context[fmap[?F] _ (pure[?F] _)] ] =>
      rewrite fmap_pure_x
    | [ |- context[ap[?F] (pure[?F] id) _] ] =>
      rewrite ap_id
    | [ |- context[ap[?F] (pure[?F] _) _] ] =>
      rewrite ap_fmap
    | [ |- context[ap[?F] (pure[?F] _)] ] =>
      rewrite ap_fmap
    | [ |- context[ap[?F] (pure[?F] _) (pure[?F] _)] ] =>
      rewrite ap_homo
    | [ |- context[_ <*> pure[?F] _] ] =>
      rewrite ap_interchange

    | [ |- context[fmap[?F] id] ] =>
      setoid_rewrite fmap_id
    | [ |- context[fmap[?F] _ (fmap[?F] _ _)] ] =>
      setoid_rewrite fmap_comp_x

    | [ |- context[fmap[?F] _ (pure[?F] _)] ] =>
      setoid_rewrite fmap_pure_x
    | [ |- context[ap[?F] (pure[?F] id) _] ] =>
      setoid_rewrite ap_id
    | [ |- context[ap[?F] (pure[?F] _) _] ] =>
      setoid_rewrite ap_fmap
    | [ |- context[ap[?F] (pure[?F] _)] ] =>
      setoid_rewrite ap_fmap
    | [ |- context[ap[?F] (pure[?F] _) (pure[?F] _)] ] =>
      setoid_rewrite ap_homo
    | [ |- context[_ <*> pure[?F] _] ] =>
      setoid_rewrite ap_interchange
    end; auto.

Require Import Coq.Setoids.Setoid.

Local Obligation Tactic := intros; simpl; apply_applicative_laws.

Program Instance Compose_ApplicativeLaws
  `{ApplicativeLaws F} `{ApplicativeLaws G} : ApplicativeLaws (F \o G).
Obligation 2. (* ap_composition *)
  (* Discharge w *)
  rewrite <- ap_comp; f_equal.
  (* Discharge v *)
  rewrite <- !ap_fmap, <- ap_comp.
  symmetry.
  rewrite <- ap_comp; f_equal.
  (* Discharge u *)
  apply_applicative_laws.
  f_equal.
  extensionality y.
  extensionality x.
  extensionality x0.
  rewrite <- ap_comp, ap_fmap.
  reflexivity.
Qed.

Program Instance Impl_ApplicativeLaws {A} : ApplicativeLaws (fun B => A -> B).

End ApplicativeLaws.

Reserved Notation "f <|> g" (at level 28, left associativity).

Class Alternative (F : Type -> Type) :=
{ alt_is_applicative :> Applicative F

; empty : forall {X}, F X
; choose : forall {X}, F X -> F X -> F X
    where "f <|> g" := (choose f g)
(* ; some : forall {X}, F X -> list (F X) *)
(* ; many : forall {X}, F X -> list (F X) *)
}.

Notation "f <|> g" := (choose f g) (at level 28, left associativity).

(* Module Import LN := ListNotations. *)

(* Program Instance list_Alternative : Alternative list := { *)
(*     empty := fun _ => []; *)
(*     choose := app *)
(* }. *)

Instance Compose_Alternative
  `{Alternative F} `{Alternative G} : Alternative (F \o G)  :=
{ empty  := fun A => @empty F _ (G A)
; choose := fun A => @choose F _ (G A) (* jww (2016-01-28): correct? *)
}.
