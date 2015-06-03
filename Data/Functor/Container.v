Require Import Hask.Prelude.
Require Import Control.Monad.
Require Import Control.Comonad.

Generalizable All Variables.

(* A container takes a set of shapes {S] and a family of types {P] indexed by
   {S]. Using these two, we may construct a box for one such shape {x : S]
   along with a function (unnamed, but let's call it {f]) that, given some
   "index" {i : P x], yields the contained element corresponding to {i], of
   type {a].

   For example, the shape of a list of type {list a] may be described by its
   length {n : nat], along with an accessor of type {Fin n -> a]. Thus:

     S = nat
     P = forall n : S, Fin n
     x : S
     f : P x -> a := fun (i : P x) => nth i <some Vector x a>

   The accessor in this case need not be a closure over {Vector x a], but is
   always isomorphic to it.

   The benefit of this abstraction is that any type representable as a
   container must be strictly positive, since its elements are demonstrably
   finite (its use is contingent on the inhabitants of {S] and {P x]). *)

Record Container `(Position : Shape -> Type) (a : Type) := {
    shape  : Shape;
    getter : Position shape -> a
}.

Arguments shape  {Shape Position a} _.
Arguments getter {Shape Position a} _ _.

Program Instance Container_Functor {S : Type} (P : S -> Type) :
  Functor (Container P) := {
  fmap := fun X Y f x =>
    {| shape  := shape x
     ; getter := fun i => f (getter x i)
     |}
}.

(* Record FocusedContainer `(Position : Shape -> Type) (a : Type) := { *)
(*   is_container :> Container Position a; *)

(*   refocus : Position (shape is_container) -> FocusedContainer Shape Position a; *)
(*   focus : Position (shape is_container) *)
(* }. *)

(* Arguments focus {Shape Position a} _. *)

(* Program Instance Container_Comonad {S : Type} (P : S -> Type) : *)
(*   Comonad (FocusedContainer P) := { *)
(*   extract   := fun _ x => getter x (focus x); *)
(*   duplicate := fun _ x => *)
(*     {| is_container := *)
(*          {| shape  := shape x *)
(*           ; getter := *)
(*      ; positions :=  *)
(*      ; focus :=  *)
(*      |} *)
(* }. *)

Definition IdentityContainer `(x : a) : Container (const unit) a :=
  {| shape  := tt
   ; getter := const x
   |}.

Program Instance IdentityContainer_Applicative :
  Applicative (Container (const unit)) := {
  pure := fun _ => IdentityContainer;
  ap   := fun _ _ f x => IdentityContainer (getter f tt (getter x tt))
}.

Program Instance IdentityContainer_Monad :
  Monad (Container (const unit)) := {
  join := fun _ x => getter x tt
}.

Inductive CFree {S : Type} (P : S -> Type) (a : Type) : Type :=
  | CPure : a -> CFree P a
  | CJoin : forall s : S, (P s -> CFree P a) -> CFree P a.

Fixpoint fold `(r : x -> y) {S : Type} `(c : forall s : S, (P s -> y) -> y)
  (fr : CFree P x) : y :=
  match fr with
    | CPure x   => r x
    | CJoin s k => c s $ fun t => fold r c (k t)
  end.

Definition retract {S : Type} `(fr : CFree P a)
  `(c : forall s : S, (P s -> a) -> a) : a := fold id c fr.

Module ContainerLaws.

Include MonadLaws.

Program Instance Container_FunctorLaws {S : Type} (P : S -> Type) :
  FunctorLaws (Container P).
Obligation 1. by case. Qed.

End ContainerLaws.