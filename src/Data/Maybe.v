Require Import Hask.Control.Monad.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Inductive Maybe (A : Type) := Nothing | Just : A -> Maybe A.
Arguments Nothing {A}.
Arguments Just {A} _.

(* Notation Maybe   := option. *)
(* Notation Nothing := None. *)
(* Notation Just    := Some. *)

Definition fromMaybe `(x : a) (my : Maybe a) : a :=
  match my with
 | Just z  => z
 | Nothing => x
  end.

Definition maybe `(x : b) `(f : a -> b) (my : Maybe a) : b :=
  match my with
 | Just z  => f z
 | Nothing => x
  end.

Definition Maybe_map `(f : X -> Y) (x : Maybe X) : Maybe Y :=
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
; pure := @Just
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

Definition isJust {a} (x : Maybe a) := if x then false else true.

Definition Maybe_choose {a} (x y : Maybe a) : Maybe a :=
  match x with
  | Nothing => y
  | Just _  => x
  end.

Instance Maybe_Alternative : Alternative Maybe := {
  empty  := @Nothing;
  choose := @Maybe_choose
  (* some := fun _ x => match x with *)
  (*   | Nothing => Nothing *)
  (*   | Just x => Just [x] *)
  (*   end; *)
  (* many := fun _ x => match x with *)
  (*   | Nothing => Just [] *)
  (*   | Just x => [x] *)
  (*   end *)
}.

Lemma Maybe_choose_spec : forall a (x y : Maybe a),
  isJust (x <|> y) = (isJust x || isJust y)%bool.
Proof.
  intros a x y.
  destruct x; auto.
Qed.