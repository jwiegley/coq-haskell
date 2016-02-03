Require Import Hask.Prelude.
Require Import Hask.Control.Monad.

Generalizable All Variables.
Set Asymmetric Patterns.

Definition FreeT (f m : Type -> Type) (a : Type) :=
  forall r, (a -> m r) -> (forall x, (x -> m r) -> f x -> m r) -> m r.

Definition iterT `{Functor f} `{Monad m}
  `(phi : f (m a) -> m a) (ft : FreeT f m a) : m a :=
  ft _ pure $ fun _ h x => phi (fmap h x).

Inductive FreeF (f : Type -> Type) (a b : Type) :=
  | Pure : a -> FreeF f a b
  | Free : f b -> FreeF f a b.

Arguments Pure {f a b} _.
Arguments Free {f a b} _.

Inductive FreeTi (f m : Type -> Type) (a : Type) :=
  | FT : forall x, (x -> FreeTi f m a) -> m (FreeF f a x) -> FreeTi f m a.

Arguments FT {f m a x} _ _.

Fixpoint iterTi `{Functor f} `{Monad m}
  `(phi : f (m a) -> m a) (ft : FreeTi f m a) : m a :=
  match ft with FT s k z =>
    y <- z ;
    match y with
      | Pure x => @pure m _ a x
      | Free x => phi $ fmap (iterTi phi \o k) x
    end
  end.

(* Definition wrap `{Functor f} `{Monad m} {a} : *)
(*   f (FreeTi f m a) -> FreeTi f m a := FT id \o pure \o Free. *)

(* Definition fromFreeT `{Functor f} `{Monad m} `(z : FreeT f m a) : *)
(*   FreeTi f m a := *)
(*   join $ z _ (pure \o Pure) $ fun _ h x => *)
(*     tt. *)

Fixpoint toFreeT `{Functor f} `{Monad m} `(ft : FreeTi f m a) : FreeT f m a :=
  fun s k h =>
    match ft with FT _ g z =>
      y <- z ;
      match y with
        | Pure x => k x
        | Free fb => h _ (fun x => toFreeT (g x) _ k h) fb
      end
    end.

Program Instance FreeT_Functor {f m} : Functor (FreeT f m) := {
  fmap := fun _ _ f k => fun _ a fr => k _ (a \o f) fr
}.

Program Instance FreeT_Applicative {f m} : Applicative (FreeT f m) := {
  pure := fun _ a => fun _ k _ => k a;
  ap   := fun _ _ fk ak => fun _ b fr =>
    fk _ (fun e => ak _ (fun d => b (e d)) fr) fr
}.

(* Program Instance FreeT_Monad {f m} : Monad (FreeT f m) := { *)
(*   join := fun _ x => fun _ k h => x _ (fun y => y _ k h) h *)
(* }. *)

Module FreeTLaws.

Include MonadLaws.

(* It's not always this easy. *)
Program Instance FreeT_FunctorLaws     : FunctorLaws (FreeT f m).
Program Instance FreeT_ApplicativeLaws : ApplicativeLaws (FreeT f m).
(* Program Instance FreeT_MonadLaws       : MonadLaws (FreeT f m). *)

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