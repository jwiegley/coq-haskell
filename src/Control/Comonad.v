Require Import Hask.Prelude.
Require Import Hask.Data.List.
Require Export Hask.Control.Applicative.

Generalizable All Variables.

Class Comonad (w : Type -> Type) := {
  is_functor :> Functor w;

  extract : forall {a : Type}, w a -> a;
  duplicate : forall {a : Type}, w a -> w (w a)
}.

Arguments extract {w _ _} _.
Arguments duplicate {w _ _} _.

Definition extend `{Comonad w} {X Y : Type} (f : (w X -> Y)) : w X -> w Y :=
  fmap f \o duplicate.

Notation "m =>> f" := (extend f m) (at level 25, left associativity).

Module ComonadLaws.

Include ApplicativeLaws.

(* Class ComonadLaws (w : Type -> Type) `{Comonad w} := { *)
(*   has_applicative_laws :> ApplicativeLaws w; *)

(*   duplicate_fmap_duplicate : forall a : Type, *)
(*     duplicate \o fmap (@duplicate w _ a) =1 duplicate \o duplicate; *)
(*   duplicate_fmap_extract : forall a : Type, *)
(*     duplicate \o fmap (extract (a:=a)) =1 id; *)
(*   duplicate_extract      : forall a : Type, duplicate \o extract =1 @id (w a); *)
(*   duplicate_fmap_fmap : forall (a b : Type) (f : a -> b), *)
(*     duplicate \o fmap (fmap f) =1 fmap f \o duplicate *)
(* }. *)

(* Corollary duplicate_fmap_duplicate_x `{ComonadLaws w} : forall a x, *)
(*   duplicate (fmap (duplicate (a:=a)) x) = duplicate (duplicate x). *)
(* Proof. exact: duplicate_fmap_duplicate. Qed. *)

(* Corollary duplicate_fmap_extract_x `{ComonadLaws w} : forall a x, *)
(*   duplicate (fmap (extract (a:=a)) x) = x. *)
(* Proof. exact: duplicate_fmap_extract. Qed. *)

(* Corollary duplicate_extract_x `{ComonadLaws w} : forall a x, *)
(*   duplicate (extract x) = @id (w a) x. *)
(* Proof. exact: duplicate_extract. Qed. *)

(* Corollary duplicate_fmap_fmap_x `{ComonadLaws w} : *)
(*   forall (a b : Type) (f : a -> b) x, *)
(*   duplicate (fmap (fmap f) x) = fmap f (duplicate x). *)
(* Proof. exact: duplicate_fmap_fmap. Qed. *)

End ComonadLaws.
