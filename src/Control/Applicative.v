Require Export Hask.Ltac.
Require Export Hask.Data.Functor.
Require Export Hask.Data.Functor.Const.

Generalizable All Variables.

Reserved Notation "f <*> g" (at level 28, left associativity).

Class Applicative (f : Type -> Type) := {
  is_functor :> Functor f;

  pure : forall a : Type, a -> f a;
  ap   : forall a b : Type, f (a -> b) -> f a -> f b
    where "f <*> g" := (ap f g)
}.

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
  fmap f \o pure = pure \o f.
Proof.
  intros a b f.
  extensionality x.
  unfold Basics.compose.
  rewrite <- ap_fmap.
  apply ap_homo.
Qed.

Corollary fmap_pure_x `{ApplicativeLaws m} : forall (a b : Type) (f : a -> b) x,
  fmap f (pure x) = pure (f x).
Proof.
  intros.
  replace (pure[m] (f x)) with ((pure[m] \o f) x).
    rewrite <- fmap_pure.
    reflexivity.
  reflexivity.
Qed.

Program Instance ApplicativeLaws_Compose
  `{ApplicativeLaws F} `{ApplicativeLaws G} : ApplicativeLaws (F \o G).
Obligation 1. (* app_identity *)
  extensionality e.
  rewrite <- ap_fmap, ap_homo, ap_id, ap_fmap, fmap_id.
  reflexivity.
Qed.
Obligation 2. (* ap_composition *)
  (* Discharge w *)
  rewrite <- ap_comp.
  f_equal.
  (* Discharge v *)
  (* -[X in _ <*> _ <*> X v]ap_fmap *)
  rewrite <- ap_fmap, <- ap_comp.
  symmetry.
  rewrite <- ap_fmap, <- ap_fmap, <- ap_comp.
  f_equal.
  (* Discharge u *)
  rewrite fmap_pure_x, ap_homo.
  repeat rewrite ap_fmap.
  repeat rewrite fmap_comp_x.
  rewrite ap_interchange, ap_fmap, fmap_comp_x.
  f_equal.
  (* Discharge compose *)
  extensionality u'.
  extensionality v'.
  rewrite <- ap_fmap.
  extensionality w'.
  rewrite ap_comp.
  reflexivity.
Qed.
Obligation 3. (* ap_homo *)
  rewrite <- ap_fmap.
  repeat rewrite ap_homo.
  reflexivity.
Qed.
Obligation 4. (* ap_interchange *)
  repeat rewrite <- ap_fmap.
  rewrite ap_interchange, ap_homo.
  repeat rewrite ap_fmap.
  rewrite fmap_comp_x.
  f_equal.
  extensionality e.
  rewrite ap_interchange, ap_fmap.
  reflexivity.
Qed.
Obligation 5. (* ap_fmap *)
  extensionality x.
  rewrite <- ap_fmap, ap_homo, ap_fmap, ap_fmap.
  reflexivity.
Qed.

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
