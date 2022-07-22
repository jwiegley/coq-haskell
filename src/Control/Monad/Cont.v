Require Import Hask.Prelude.
Require Import Hask.Control.Monad.
Require Import Hask.Data.Functor.Identity.
Require Import Hask.Data.Functor.Yoneda.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition Cont (R A : Type) : Type := (A -> R) -> R.

Definition Cont_map {R X Y} (f : X -> Y) (k : Cont R X) : Cont R Y :=
  k \o (flip compose f).

#[export]
Instance Cont_Functor {R} : Functor (Cont R) :=
{ fmap := @Cont_map R
}.
(* jww (2015-06-17): NYI
Proof.
  - (* fun_identity *)
    intros. extensionality x. compute. destruct x; reflexivity.
  - (* fun_composition *)
    intros. extensionality x. compute. destruct x; reflexivity.
Defined.
*)

Definition Cont_apply {R X Y} (kf : Cont R (X -> Y)) (kx : Cont R X)
  : Cont R Y :=
  fun h => kf (fun f' =>
    kx (fun x' => h (f' x'))).

#[export]
Instance Cont_Applicative {R} : Applicative (Cont R) :=
{ is_functor := Cont_Functor
; pure := fun A x => fun k => k x
; ap := @Cont_apply R
}.
(* jww (2015-06-17): NYI
Proof.
  - (* app_identity *)
    intros. extensionality x. compute. destruct x; reflexivity.
  - (* app_composition *)
    intros. compute.
    destruct u.
      destruct v; reflexivity.
  - (* app_homomorphism *)
    intros. compute. reflexivity.
  - (* app_interchange *)
    intros. compute. destruct u; reflexivity.
  - (* app_fmap_unit *)
    intros. extensionality x. compute. destruct x; reflexivity.
Defined.
*)

Definition Cont_join {R X} (k : Cont R (Cont R X)) : Cont R X :=
  fun h => k (fun km => km (fun x' => h x')).

#[export]
Instance Cont_Monad {R} : Monad (Cont R) :=
{ is_applicative := Cont_Applicative
; join := @Cont_join R
}.
(* jww (2015-06-17): NYI
Proof.
  - (* monad_law_1 *)
    intros. extensionality x. compute.
    destruct x.
    f_equal. extensionality p.
    f_equal. extensionality q.
    destruct q.
    f_equal.
  - (* monad_law_2 *)
    intros. extensionality x. compute.
    destruct x; reflexivity.
  - (* monad_law_3 *)
    intros. extensionality x. compute.
    destruct x; reflexivity.
  - (* monad_law_4 *)
    intros. extensionality x. compute.
    destruct x.
    f_equal. extensionality p.
    f_equal. extensionality q.
    destruct q.
    f_equal.
Defined.
*)

Lemma Cont_parametricity :
  forall A B C (f : B -> C) (g : A -> B) (k : forall r, Cont r A),
    f (k B g) = k C (f \o g).
Proof.
  intros.
  Import YonedaLaws.
  pose proof (@Yoneda_parametricity Identity _ _ _ _ k f).
  apply H.
Qed.
