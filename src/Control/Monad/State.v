Require Import Hask.Prelude.
Require Import Hask.Control.Monad.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************
 * The State Monad
 *)

Definition State (s a : Type) := s -> (a * s).

Definition get  {s : Type}     : State s s := fun i => (i, i).
Definition gets {s a : Type} f : State s a := fun s => (f s, s).
Definition put  {s : Type} x   : State s unit := fun _ => (tt, x).

Definition modify {s : Type} (f : s -> s) : State s unit := fun i => (tt, f i).

Program Instance State_Functor {s : Type} : Functor (State s) := {
  fmap := fun A B f (x : State s A) => fun st => match x st with
    | (a,st') => (f a, st')
    end
}.

Program Instance State_Applicative {s : Type} : Applicative (State s) := {
  pure := fun _ x => fun st => (x, st);

  ap := fun _ _ f x => fun st => match f st with
    | (f', st') =>
        match x st' with
        | (x', st'') => (f' x', st'')
        end
    end
}.

Program Instance State_Monad {s : Type} : Monad (State s) := {
  join := fun _ x => fun st => match x st with
    | (y, st') => match y st' with
      | (a, st'') => (a, st'')
      end
    end
}.

Module StateLaws.

Include MonadLaws.

Require Import FunctionalExtensionality.

Program Instance State_FunctorLaws {s : Type} : FunctorLaws (State s).
Obligation 1.
  move=> x.
  extensionality st.
  by case: (x st).
Qed.
Obligation 2.
  rewrite /funcomp => x.
  extensionality st.
  by case: (x st).
Qed.

Program Instance State_Applicative {s : Type} : ApplicativeLaws (State s).
Obligation 1.
  move=> x.
  extensionality st.
  by case: (x st).
Qed.
Obligation 2.
  extensionality st.
  case: (u st) => f' st'.
  case: (v st') => f'' st''.
  by case: (w st'').
Qed.

Program Instance State_Monad {s : Type} : MonadLaws (State s).
Obligation 1.
  move=> f.
  extensionality st.
  rewrite /funcomp /=.
  case: (f st) => f' st'.
  case: (f' st') => f'' st''.
  by case: (f'' st'') => f''' st'''.
Qed.
Obligation 2.
  move=> f.
  extensionality st.
  rewrite /funcomp /=.
  by case: (f st) => f' st'.
Qed.
Obligation 3.
  move=> f.
  extensionality st.
  rewrite /funcomp /=.
  by case: (f st) => f' st'.
Qed.
Obligation 4.
  move=> x.
  extensionality st.
  rewrite /funcomp /=.
  case: (x st) => f' st'.
  by case: (f' st') => f'' st''.
Qed.

End StateLaws.
