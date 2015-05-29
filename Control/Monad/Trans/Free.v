Require Import Hask.Prelude.
Require Import Hask.Control.Monad.
Require Import Hask.Data.Functor.Container.

Generalizable All Variables.

Inductive FreeCon `(P : A -> Type) (a b : Type) :=
  | PureC : a -> FreeCon P a b
  | FreeC : Container P b -> FreeCon P a b.

Arguments PureC {A P a b} _.
Arguments FreeC {A P a b} _.

Inductive FreeConT `(PF : CF -> Type) `{Functor (Container PF)}
  `(PM : CM -> Type) `{Monad (Container PM)} (a : Type) :=
  FCT of Container PM (FreeCon PF a (FreeConT PF PM a)).

Arguments FCT {CF PF _ CM PM _ a} _.

Definition FreeT (f m : Type -> Type) (a : Type) :=
  forall r, (a -> m r) -> (forall x, (x -> m r) -> f x -> m r) -> m r.

Program Instance FreeT_Functor {f m} : Functor (FreeT f m) := {
  fmap := fun _ _ f k => fun _ a fr => k _ (a \o f) fr
}.

Program Instance FreeT_Applicative {f m} : Applicative (FreeT f m) := {
  pure := fun _ a => fun _ k _ => k a;
  ap   := fun _ _ fk ak => fun _ b fr =>
    fk _ (fun e => ak _ (fun d => b (e d)) fr) fr
}.

Program Instance FreeT_Monad {f m} : Monad (FreeT f m) := {
  join := fun _ x => fun _ k g => undefined
}.

Section FreeT.

Context `{HF : Functor f}.
Context `{HM : Monad m}.

Variable CF : Type.
Variable PF : CF -> Type.
Context `{Functor (Container PF)}.

Variable CM : Type.
Variable PM : CM -> Type.
Context `{Monad (Container PM)}.

(* Definition toFreeConT `(t : FreeT f id a) : FreeConT PF (const unit) a := *)
(*   FCT $ IdentityContainer $ t _ (pure \o PureC) (fun _ k x => k x). *)

Axiom ft_ind : forall (a : Type) (P : FreeT f id a -> Prop),
   (forall (h : a), P (fun _ p _ => p h)) ->
   (forall x (h : forall r, x -> r) (b : f x) (t : FreeT f id a),
      P t -> P (fun s _ k => k x (h s) b)) ->
   forall t : FreeT f id a, P t.

End FreeT.