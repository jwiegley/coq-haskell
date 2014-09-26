Require Export Applicative.

Generalizable All Variables.

Reserved Notation "f <|> g" (at level 28, left associativity).

Class Alternative (F : Type -> Type) :=
{ alt_is_applicative :> Applicative F

; empty : forall {X}, F X
; choose : forall {X}, F X -> F X -> F X
    where "f <|> g" := (choose f g)
(* ; some : forall {X}, F X -> list (F X) *)
(* ; many : forall {X}, F X -> list (F X) *)
}.

Notation "f <|> g" := (choose f g) (at level 28, left associativity).

Program Instance option_Alternative : Alternative option := {
    empty := fun _ => None;
    choose := fun _ x y => match x with
      | None => y
      | Some _ => x
      end
    (* some := fun _ x => match x with *)
    (*   | None => None *)
    (*   | Some x => Some [x] *)
    (*   end; *)
    (* many := fun _ x => match x with *)
    (*   | None => Some [] *)
    (*   | Some x => [x] *)
    (*   end *)
}.

Module Import LN := ListNotations.

Program Instance list_Alternative : Alternative list := {
    empty := fun _ => [];
    choose := app
}.
