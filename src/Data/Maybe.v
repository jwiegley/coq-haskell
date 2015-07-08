Require Import Hask.Ssr.
Require Import Hask.Control.Monad.

Generalizable All Variables.

Notation Maybe := option.
Notation Nothing := None.
Notation Just := Some.

Definition Maybe_map {X Y} (f : X -> Y) (x : Maybe X) : Maybe Y :=
  match x with
  | Nothing => Nothing
  | Just x' => Just (f x')
  end.

Instance Maybe_Functor : Functor Maybe :=
{ fmap := @Maybe_map
}.

Definition Maybe_apply {X Y} (f : Maybe (X -> Y)) (x : Maybe X) : Maybe Y :=
  match f with
  | Nothing => Nothing
  | Just f' => match x with
    | Nothing => Nothing
    | Just x' => Just (f' x')
    end
  end.

Instance Maybe_Applicative : Applicative Maybe :=
{ is_functor := Maybe_Functor
; pure := Just
; ap := @Maybe_apply
}.

Definition Maybe_join {X} (x : Maybe (Maybe X)) : Maybe X :=
  match x with
  | Nothing => Nothing
  | Just Nothing => Nothing
  | Just (Just x') => Just x'
  end.

Instance Maybe_Monad : Monad Maybe :=
{ is_applicative := Maybe_Applicative
; join := @Maybe_join
}.

(* jww (2015-06-17): NYI
Ltac simple_solver :=
  intros;
  try extensionality e;
  compute;
  repeat (
    match goal with
    | [ |- context f [match ?X with _ => _ end] ] =>
      is_var X; destruct X; auto
    end);
  auto.

(** By registering our simple_solver as the obligation tactic, all our law
    obligations will be taken care of for us automatically by the Ltac
    scripts above. *)
Obligation Tactic := simple_solver.
*)

Definition isJust {a} (x : option a) := if x is Some _ then true else false.

Definition option_map `(f : a -> b) (x : option a) : option b :=
  match x with
  | None => None
  | Some x => Some (f x)
  end.

Definition option_choose {a} (x y : option a) : option a :=
  match x with
  | None => y
  | Some _ => x
  end.

Instance option_Alternative : Alternative option := {
  empty := fun _ => None;
  choose := fun _ => option_choose
  (* some := fun _ x => match x with *)
  (*   | None => None *)
  (*   | Some x => Some [x] *)
  (*   end; *)
  (* many := fun _ x => match x with *)
  (*   | None => Some [] *)
  (*   | Some x => [x] *)
  (*   end *)
}.
