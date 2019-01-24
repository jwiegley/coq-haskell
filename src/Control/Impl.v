Require Import Hask.Data.Functor.
Require Import Hask.Control.Applicative.
Require Import Hask.Control.Monad.
Require Import Hask.Control.Compose.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Instance Impl_Functor {A} : Functor (fun B => A -> B) := {
  fmap := fun A B f run => fun xs => f (run xs)
}.

Instance Impl_Applicative {A} : Applicative (fun B => A -> B) := {
  pure := fun _ x => fun _ => x;
  ap   := fun _ _ runf runx => fun xs => runf xs (runx xs)
}.

Instance Impl_Monad {A} : Monad (fun B => A -> B) := {
  join := fun A run => fun xs => run xs xs
}.

Program Instance Impl_Monad_Distributes `{Monad N} :
  @Monad_Distributes (fun B => A -> B) Impl_Monad N is_applicative.
Obligation 1.
  exact (X >>= fun f => f X0).
Defined.

Module ImplMonadLaws.

Import MonadLaws.

Program Instance Impl_FunctorLaws {A} : FunctorLaws (fun B => A -> B).
Program Instance Impl_ApplicativeLaws {A} : ApplicativeLaws (fun B => A -> B).
Program Instance Impl_MonadLaws : MonadLaws (fun B => A -> B).

Require Import FunctionalExtensionality.

Program Instance Impl_Monad_DistributesLaws `{MonadLaws N} :
  @Monad_DistributesLaws (fun B => A -> B) N _ Impl_Monad is_applicative
                         Impl_Monad_Distributes.
Obligation 1.
  unfold Impl_Monad_Distributes_obligation_1, comp, bind, id.
  extensionality x.
  extensionality x0.
  simpl.
  rewrite <- join_fmap_fmap_x, !fmap_comp_x.
  reflexivity.
Qed.
Obligation 2.
  unfold Impl_Monad_Distributes_obligation_1, comp, bind, id.
  extensionality x.
  extensionality x0.
  simpl.
  rewrite fmap_pure_x, join_pure_x.
  reflexivity.
Qed.
Obligation 3.
  unfold Impl_Monad_Distributes_obligation_1, comp, bind, id.
  extensionality x.
  extensionality x0.
  simpl.
  rewrite fmap_comp_x, join_fmap_pure_x.
  reflexivity.
Qed.
Obligation 4.
  unfold Impl_Monad_Distributes_obligation_1, comp, bind, id.
  extensionality x.
  extensionality x0.
  simpl.
  rewrite <- join_fmap_fmap_x, <- join_fmap_join_x, !fmap_comp_x.
  reflexivity.
Qed.

End ImplMonadLaws.
