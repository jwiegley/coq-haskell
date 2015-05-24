Require Import Hask.Prelude.
Require Export Hask.Data.Functor.

Generalizable All Variables.

Reserved Notation "f <*> g" (at level 28, left associativity).

Class Applicative (f : Type -> Type) := {
  is_functor :> Functor f;

  pure : forall {a : Type}, a -> f a;
  ap   : forall {a b : Type}, f (a -> b) -> f a -> f b
    where "f <*> g" := (ap f g)
}.

Arguments pure {f _ _} _.
Arguments ap   {f _ _ _} _ x.

Notation "f <*> g" := (ap f g) (at level 28, left associativity).

Definition liftA2 `{Applicative m} {A B C : Type}
  (f : A -> B -> C) (x : m A) (y : m B) : m C := ap (fmap f x) y.

Instance Applicative_Compose (F : Type -> Type) (G : Type -> Type)
  `{Applicative F} `{Applicative G} : Applicative (F \o G)  :=
{ is_functor := Functor_Compose (F:=F) (G:=G)
; pure := fun A   => @pure F _ (G A) \o @pure G _ A
; ap   := fun A B => ap \o fmap (@ap G _ A B)
}.

Module ApplicativeLaws.

Include FunctorLaws.

Require Import FunctionalExtensionality.

Class ApplicativeLaws (f : Type -> Type) `{H : Applicative f} := {
  has_functor_laws :> FunctorLaws f;

  ap_id : forall a : Type, ap (pure (@id a)) =1 id;
  ap_comp : forall (a b c : Type) (v : f (a -> b)) (u : f (b -> c)) (w : f a),
    pure compose <*> u <*> v <*> w = u <*> (v <*> w);
  ap_homo : forall (a b : Type) (x : a) (f : a -> b),
    pure f <*> pure x = pure (f x);
  ap_interchange : forall (a b : Type) (y : a) (u : f (a -> b)),
    u <*> pure y = pure (fun f => f y) <*> u;

  ap_fmap : forall (a b : Type) (f : a -> b),
    ap (pure f) =1 @fmap _ is_functor _ _ f
}.

Corollary fmap_pure `{ApplicativeLaws m} : forall (a b : Type) (f : a -> b),
  fmap f \o pure =1 pure \o f.
Proof.
  move=> a b f x.
  rewrite /funcomp -ap_fmap.
  exact: ap_homo.
Qed.

Corollary fmap_pure_x `{ApplicativeLaws m} : forall (a b : Type) (f : a -> b) x,
  fmap f (pure x) = pure (f x).
Proof. exact: fmap_pure. Qed.

(* Program Instance Applicative_Compose (F : Type -> Type) (G : Type -> Type) *)
(*   `{ApplicativeLaws F} `{ApplicativeLaws G} : ApplicativeLaws (F \o G). *)
(* Obligation 1. (* app_identity *) *)
(*   move=> e. *)
(*   rewrite <- ap_fmap_unit. *)
(*   rewrite ap_homomorphism. *)
(*   rewrite ap_identity. *)
(*   rewrite ap_fmap_unit. *)
(*   rewrite fun_identity. *)
(*   reflexivity. *)
(* Qed. *)
(* Obligation 2. (* ap_composition *) *)
(*   intros. *)
(*   (* apply <$> (apply <$> (apply <$> pure (pure compose) <*> u) <*> v) <*> w = *)
(*      apply <$> u <*> (apply <$> v <*> w) *) *)
(*   unfold compose_apply, compose_pure, compose. *)
(*   rewrite <- ap_composition. *)
(*   f_equal. *)
(*   rewrite_ap_homomorphisms. *)
(*   rewrite fun_composition_x. *)
(*   rewrite ap_split. *)
(*   rewrite ap_split. *)
(*   rewrite <- ap_naturality. *)
(*   rewrite fun_composition_x. *)
(*   rewrite fun_composition_x. *)
(*   f_equal. extensionality x. *)
(*   destruct x. *)
(*   unfold compose at 3. *)
(*   unfold ap_merge. *)
(*   rewrite uncurry_works. *)
(*   unfold compose at 1. *)
(*   unfold compose at 1. *)
(*   rewrite uncurry_works. *)
(*   extensionality e. *)
(*   rewrite <- ap_fmap_unit. *)
(*   rewrite ap_composition. *)
(*   unfold compose. *)
(*   reflexivity. *)

(* - (* ap_homomorphism *) intros. *)
(*   unfold compose_apply, compose_pure, compose. *)
(*   rewrite <- ap_fmap_unit. *)
(*   repeat (rewrite ap_homomorphism). *)
(*   reflexivity. *)

(* - (* ap_interchange *) intros. *)
(*   unfold compose_apply, compose_pure, compose. *)
(*   repeat (rewrite <- ap_fmap_unit). *)
(*   rewrite ap_interchange. *)
(*   rewrite_ap_homomorphisms. *)
(*   rewrite fun_composition_x. *)
(*   unfold compose. f_equal. extensionality e. *)
(*   rewrite <- ap_fmap_unit. *)
(*   rewrite ap_interchange. *)
(*   reflexivity. *)

(* - (* ap_fmap_unit *) intros. *)
(*   unfold compose_apply, compose_pure, compose. *)
(*   rewrite_ap_homomorphisms. *)
(*   reflexivity. *)

End ApplicativeLaws.
