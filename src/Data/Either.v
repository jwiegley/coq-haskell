Require Import Hask.Control.Monad.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Notation Either := sum (only parsing).
Notation Left   := inl (only parsing).
Notation Right  := inr (only parsing).

Definition isLeft  `(x : a + b) : bool := if x then true else false.
Definition isRight `(x : a + b) : bool := if x then false else true.

Definition either `(f : a -> c) `(g : b -> c) (x : a + b) : c :=
  match x with
  | inl a => f a
  | inr b => g b
  end.

Definition mapLeft `(f : a -> c) `(x : a + b) : c + b :=
  match x with
  | inl l => inl (f l)
  | inr r => inr r
  end.

Definition Either_map {E X Y} (f : X -> Y) (x : Either E X) : Either E Y :=
  match x with
  | Left e   => Left e
  | Right x' => Right (f x')
  end.

Definition Either_apply {E X Y} (f : Either E (X -> Y)) (x : Either E X)
  : Either E Y :=
  match f with
  | Left e   => Left e
  | Right f' => match x with
    | Left e   => Left e
    | Right x' => Right (f' x')
    end
  end.

Definition Either_join {E X} (x : Either E (Either E X)) : Either E X :=
  match x with
  | Left e           => Left e
  | Right (Left e)   => Left e
  | Right (Right x') => Right x'
  end.

Instance Either_Functor {E} : Functor (Either E) :=
{ fmap := @Either_map E
}.
(* jww (2015-06-17): NYI
Proof.
  - (* fun_identity *)
    intros. extensionality x. compute. destruct x; reflexivity.
  - (* fun_composition *)
    intros. extensionality x. compute. destruct x; reflexivity.
Defined.
*)

Instance Either_Applicative {E} : Applicative (Either E) :=
{ is_functor := Either_Functor
; pure := @Right E
; ap := @Either_apply E
}.
(* jww (2015-06-17): NYI
Proof.
  - (* app_identity *)
    intros. extensionality x. compute. destruct x; reflexivity.
  - (* app_composition *)
    intros. compute.
    destruct u.
      destruct v; reflexivity.
      destruct v. reflexivity. destruct w; reflexivity.
  - (* app_homomorphism *)
    intros. compute. reflexivity.
  - (* app_interchange *)
    intros. compute. destruct u; reflexivity.
  - (* app_fmap_unit *)
    intros. extensionality x. compute. destruct x; reflexivity.
Defined.
*)

Instance Either_Monad {E} : Monad (Either E) :=
{ is_applicative := Either_Applicative
; join := @Either_join E
}.
(* jww (2015-06-17): NYI
Proof.
  - (* monad_law_1 *)
    intros. extensionality x. compute.
    destruct x.
      reflexivity.
      destruct e.
        reflexivity.
        destruct e; reflexivity.
  - (* monad_law_2 *)
    intros. extensionality x. compute.
    destruct x; reflexivity.
  - (* monad_law_3 *)
    intros. extensionality x. compute.
    destruct x; reflexivity.
  - (* monad_law_4 *)
    intros. extensionality x. compute.
    destruct x.
      reflexivity.
      destruct e; reflexivity.
Defined.
*)