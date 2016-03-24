Require Import Hask.Prelude.
Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.Trans.Class.
Require Import Hask.Control.Monad.Morph.

Generalizable All Variables.

Definition ReaderT (X : Type) (M : Type -> Type) (Y : Type) : Type :=
  X -> M Y.

Definition runReaderT {E M A} (r : ReaderT E M A) := r.

Program Instance ReaderT_Functor `{Functor m} {E} : Functor (ReaderT E m) :=
  @Compose_Functor _ Impl_Functor m _.

Program Instance ReaderT_Applicative `{Applicative m} {E} :
  Applicative (ReaderT E m) :=
  @Compose_Applicative _ m Impl_Applicative _.

Program Instance ReaderT_Monad `{Monad m} {E} : Monad (ReaderT E m) :=
  @Compose_Monad _ Impl_Monad m _ Impl_Monad_Distributes.

Instance ReaderT_MonadTrans {E} : MonadTrans (ReaderT E) :=
{ lift := fun _ _ _ _ => fun v _ => v
}.

Program Instance ReaderT_MFunctor {E} : MFunctor (ReaderT E) :=
{ hoist := fun _ _ _ _ _ nat => fun v1 v2 => nat _ (v1 v2)
}.

Module ReaderTLaws.

Import MonadLaws.

Program Instance ReaderT_FunctorLaws `{FunctorLaws m} {E} :
  FunctorLaws (ReaderT E m) :=
  @Compose_FunctorLaws _ Impl_Functor Impl_FunctorLaws m _ _.

Program Instance ReaderT_ApplicativeLaws `{ApplicativeLaws m} {E} :
  ApplicativeLaws (ReaderT E m) :=
  @Compose_ApplicativeLaws _ _ Impl_ApplicativeLaws m _ _.

Program Instance ReaderT_MonadLaws `{MonadLaws m} {E} :
  MonadLaws (ReaderT E m) :=
  @Compose_MonadLaws _ Impl_Monad m _ _ Impl_Monad_DistributesLaws.

End ReaderTLaws.

Class MonadReader (r : Type) (m : Type -> Type) `{Monad m} := {
  ask    : m r;
  local  : forall a, (r -> r) -> m a -> m a;
  reader : forall a, (r -> a) -> m a
}.

Program Instance ReaderT_MonadReader {E} `{Monad m} :
  MonadReader E (ReaderT E m) := {
  ask    := pure;
  local  := fun _ f m => fun v => m (f v);
  reader := fun _ f => fun v => pure (f v)
}.
