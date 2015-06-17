Require Import Hask.Ssr.
Require Export Hask.Data.Functor.

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

Notation "pure/ M" := (@pure M _ _) (at level 28).
Notation "pure/ M N" := (@pure (fun X => M (N X)) _ _) (at level 26).

Notation "ap[ M ]  f" := (@ap M _ _ _ f) (at level 28).
Notation "ap[ M N ]  f" := (@ap (fun X => M (N X)) _ _ _ f) (at level 26).
Notation "ap[ M N O ]  f" := (@ap (fun X => M (N (O X))) _ _ _ f) (at level 24).

Infix "<*>" := ap (at level 28, left associativity).

(* Notation "[| f x y .. z |]" := (.. (f <$> x <*> y) .. <*> z) *)
(*     (at level 9, left associativity, f at level 9, *)
(*      x at level 9, y at level 9, z at level 9). *)

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

Class ApplicativeLaws (f : Type -> Type) `{Applicative f} := {
  has_functor_laws :> FunctorLaws f;

  ap_id : forall a : Type, ap (pure (@id a)) =1 id;
  ap_comp : forall (a b c : Type) (v : f (a -> b)) (u : f (b -> c)) (w : f a),
    pure (fun f g x => f (g x)) <*> u <*> v <*> w = u <*> (v <*> w);
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

Corollary ap_id_ext `{ApplicativeLaws f} : forall a : Type,
  ap (pure (@id a)) = id.
Proof.
  move=> a.
  extensionality x.
  exact: ap_id.
Qed.

Corollary ap_fmap_ext `{ApplicativeLaws F} : forall (a b : Type) (f : a -> b),
  ap (pure f) = @fmap _ is_functor _ _ f.
Proof.
  move=> a b f.
  extensionality x.
  exact: ap_fmap.
Qed.

Program Instance ApplicativeLaws_Compose (F : Type -> Type) (G : Type -> Type)
  `{ApplicativeLaws F} `{ApplicativeLaws G} : ApplicativeLaws (F \o G).
Obligation 1. (* app_identity *)
  move=> e.
  by rewrite -ap_fmap ap_homo ap_id_ext ap_fmap fmap_id.
Qed.
Obligation 2. (* ap_composition *)
  (* Discharge w *)
  rewrite -ap_comp.
  f_equal.
  (* Discharge v *)
  rewrite -ap_fmap_ext -ap_comp -[X in _ <*> _ <*> X v]ap_fmap_ext -ap_comp.
  f_equal.
  (* Discharge u *)
  rewrite fmap_pure_x ap_homo !ap_fmap !fmap_comp_x ap_interchange
          ap_fmap fmap_comp_x ap_fmap_ext.
  f_equal.
  (* Discharge compose *)
  extensionality u'.
  extensionality v'.
  rewrite -ap_fmap_ext.
  extensionality w'.
  by rewrite /= ap_comp.
Qed.
Obligation 3. (* ap_homo *)
  by rewrite -ap_fmap !ap_homo.
Qed.
Obligation 4. (* ap_interchange *)
  rewrite -!ap_fmap ap_interchange ap_homo !ap_fmap fmap_comp_x.
  f_equal.
  extensionality e.
  by rewrite ap_interchange.
Qed.
Obligation 5. (* ap_fmap *)
  move=> x.
  by rewrite -ap_fmap ap_homo ap_fmap ap_fmap_ext.
Qed.

End ApplicativeLaws.
