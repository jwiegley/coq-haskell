Require Import Hask.Prelude.
Require Import Hask.Control.Monad.

Generalizable All Variables.

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
  join := fun _ x => fun _ k h => x _ (fun y => y _ k h) h
}.

Module FreeTLaws.

Include MonadLaws.

(* It's not always this easy. *)
Program Instance FreeT_FunctorLaws     : FunctorLaws (FreeT f m).
Program Instance FreeT_ApplicativeLaws : ApplicativeLaws (FreeT f m).
Program Instance FreeT_MonadLaws       : MonadLaws (FreeT f m).

End FreeTLaws.

Section FreeT.

Context `{Functor f}.
Context `{Monad m}.

Axiom ft_ind : forall (a : Type) (P : FreeT f id a -> Prop),
   (forall (h : a), P (fun _ p _ => p h)) ->
   (forall x (h : forall r, x -> r) (b : f x) (t : FreeT f id a),
      P t -> P (fun s _ k => k x (h s) b)) ->
   forall t : FreeT f id a, P t.

End FreeT.