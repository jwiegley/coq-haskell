Require Import Hask.Control.Iso.

Generalizable All Variables.

Instance LTuple_Isomorphism {A} : (unit * A) ≅ A :=
{ iso_to   := @snd unit A
; iso_from := pair tt
}.
(* jww (2015-06-17): NYI
Obligation 1. (* iso_to *)
  intros. extensionality x. destruct x. compute. destruct u. reflexivity.
Defined.
*)

Instance RTuple_Isomorphism {A} : (A * unit) ≅ A :=
{ iso_to   := @fst A unit
; iso_from := fun x => (x, tt)
}.
(* jww (2015-06-17): NYI
Obligation 1. (* iso_to *)
  intros. extensionality x. destruct x. compute. destruct u. reflexivity.
Defined.
*)

Definition tuple_swap_a_bc_to_ab_c {A B C} (x : A * (B * C)) : A * B * C :=
  match x with (a, (b, c)) => ((a, b), c) end.

Definition tuple_swap_ab_c_to_a_bc {A B C} (x : A * B * C) : A * (B * C) :=
  match x with ((a, b), c) => (a, (b, c)) end.

Definition left_triple {A B C} (x : A) (y : B) (z : C) : A * B * C :=
  ((x, y), z).

Definition right_triple {A B C} (x : A) (y : B) (z : C) : A * (B * C) :=
  (x, (y, z)).

Instance Tuple_Assoc {A B C} : (A * B * C) ≅ (A * (B * C)) :=
{ iso_to   := tuple_swap_ab_c_to_a_bc
; iso_from := tuple_swap_a_bc_to_ab_c
}.
(* jww (2015-06-17): NYI
Obligation 1. (* iso_to *)
  intros.
  extensionality x.
  unfold compose.
  destruct x.
  destruct p.
  unfold id.
  unfold tuple_swap_a_bc_to_ab_c, tuple_swap_ab_c_to_a_bc.
  reflexivity.
Defined.
Obligation 2. (* iso_from *)
  intros.
  extensionality x.
  unfold compose.
  destruct x.
  destruct p.
  unfold id.
  unfold tuple_swap_a_bc_to_ab_c, tuple_swap_ab_c_to_a_bc.
  reflexivity.
Defined.
*)

Definition first `(f : a -> b) `(x : a * z) : b * z :=
  match x with (a, z) => (f a, z) end.

Definition second `(f : a -> b) `(x : z * a) : z * b :=
  match x with (z, b) => (z, f b) end.

Definition curry `(f : a -> b -> c) (x : (a * b)) : c :=
  match x with (a, b) => f a b end.

Definition uncurry {X Y Z} (f : X -> Y -> Z) (xy : X * Y) : Z :=
  match xy with (x, y) => f x y end.

Theorem uncurry_works : forall {X Y Z} (x : X) (y : Y) (f : X -> Y -> Z),
  uncurry f (x, y) = f x y.
Proof. reflexivity. Qed.
