Require Export FunctionalExtensionality.

Close Scope nat_scope.

(* Simple identity. *)

Definition id {X} (a : X) : X := a.

Hint Unfold id.

(* Function composition. *)

Definition compose {A B C} (f : B -> C) (g : A -> B) (x : A) : C := f (g x).

Hint Unfold compose.

Notation "f ∘ g" := (compose f g) (at level 69, right associativity).

Theorem comp_id_left : forall {A B} (f : A -> B), id ∘ f = f.
Proof. reflexivity. Qed.

Hint Resolve comp_id_left.

Theorem comp_id_right : forall {A B} (f : A -> B), f ∘ id = f.
Proof. reflexivity. Qed.

Hint Resolve comp_id_right.

Theorem comp_assoc : forall {A B C D} (f : C -> D) (g : B -> C) (h : A -> B),
  f ∘ g ∘ h = (f ∘ g) ∘ h.
Proof. reflexivity. Qed.

Hint Resolve comp_assoc.

Theorem uncompose : forall {A B C} (f : B -> C) (g : A -> B) (x : A) (y : C),
  (f ∘ g) x = f (g x).
Proof. reflexivity. Qed.

Ltac uncompose k :=
  rewrite <- (uncompose k);
  repeat (rewrite <- comp_assoc).

(* Utility functions. *)

Definition flip {X Y Z} (f : X -> Y -> Z) (y : Y) (x : X) : Z := f x y.

Definition call {X Y} (f : X -> Y) (x : X) : Y := f x.

Theorem flip_call : forall {X Y} (f : X -> Y) (x : X),
  f x = flip call x f.
Proof. reflexivity. Qed.