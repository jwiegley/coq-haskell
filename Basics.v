Require Export Coq.Program.Basics.
Require Export FunctionalExtensionality.

Close Scope nat_scope.
Open Scope program_scope.

Hint Unfold id.
Hint Unfold compose.

Theorem comp_id_left : forall {A B} (f : A -> B), id ∘ f = f.
Proof. reflexivity. Qed.

Hint Resolve comp_id_left.

Theorem comp_id_right : forall {A B} (f : A -> B), f ∘ id = f.
Proof. reflexivity. Qed.

Hint Resolve comp_id_right.

Theorem comp_assoc : forall {A B C D} (f : C -> D) (g : B -> C) (h : A -> B),
  f ∘ (g ∘ h) = (f ∘ g) ∘ h.
Proof. reflexivity. Qed.

Hint Resolve comp_assoc.

Theorem uncompose : forall {A B C} (f : B -> C) (g : A -> B) (x : A) (y : C),
  (f ∘ g) x = f (g x).
Proof. reflexivity. Qed.

Ltac uncompose k :=
  rewrite <- (uncompose k);
  repeat (rewrite <- comp_assoc).
