(* Require Import Data.Functor.Identity. *)
Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.Trans.State.

Generalizable All Variables.
Unset Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class FunDep {T : Type} (m1 m2 : T).

Class MonadBase (b : Type -> Type) `{Monad b} (m : Type -> Type) `{Monad m}
      `{FunDep (Type -> Type) m b} := {
  liftBase : forall a, b a -> m a
}.
Arguments liftBase {b _ m _ _ _ a} _.

(* #[export] *)
(* Instance FunDep_Id_Id : FunDep Identity Identity. *)

(* #[export] *)
(* Instance MonadBase_Id_Id : MonadBase Identity Identity := { *)
(*   liftBase := @id *)
(* }. *)

#[export]
Program Instance StateT_m_b {s : Type} {m b : Type -> Type}
         `{FunDep (Type -> Type) m b} :
  FunDep (StateT s m) b.

#[export]
Instance MonadBase_StateT {s : Type} {m b : Type -> Type}
         `{B : MonadBase b m} : MonadBase b (StateT s m) := {
  liftBase := fun A x st =>
                res <- liftBase x;
                @pure m _ (A * s) (res, st)
}.
