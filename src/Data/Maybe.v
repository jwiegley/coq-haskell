Require Import Hask.Ssr.
Require Import Hask.Control.Monad.

Generalizable All Variables.

Inductive Maybe (a : Type) : Type :=
  | Just : a -> Maybe a
  | Nothing : Maybe a.

(* Notation Maybe := option. *)
(* Notation Nothing := None. *)
(* Notation Just := Some. *)

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

Set Printing Universes.

Definition Maybe_map `(f : X -> Y) (x : Maybe X) : Maybe Y :=
  match x with
  | Nothing => @Nothing Y
  | Just x' => @Just Y (f x')
  end.

Instance Maybe_Functor : Functor Maybe :=
{ fmap := @Maybe_map
}.

Definition Maybe_apply {X Y} (f : Maybe (X -> Y)) (x : Maybe X) : Maybe Y :=
  match f with
  | Nothing => @Nothing Y
  | Just f' => match x with
    | Nothing => @Nothing Y
    | Just x' => @Just Y (f' x')
    end
  end.

Instance Maybe_Applicative : Applicative Maybe :=
{ is_functor := Maybe_Functor
; pure := Just
; ap := @Maybe_apply
}.

Definition Maybe_join {X} (x : Maybe (Maybe X)) : Maybe X :=
  match x with
  | Nothing => @Nothing X
  | Just Nothing => @Nothing X
  | Just (Just x') => @Just X x'
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

Definition isJust {a} (x : Maybe a) := if x is Just _ then true else false.

Definition Maybe_choose {a} (x y : Maybe a) : Maybe a :=
  match x with
  | Nothing => y
  | Just _ => x
  end.

Instance Maybe_Alternative : Alternative Maybe := {
  empty := fun T => @Nothing T;
  choose := fun _ => Maybe_choose
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
  isJust (x <|> y) = isJust x || isJust y.
Proof. by move=> a [x|] [y|] //=. Qed.
