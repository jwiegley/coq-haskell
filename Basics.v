Require Export Coq.Classes.Morphisms.
Require Export Coq.Program.Basics.
Require Export Coq.Program.Tactics.
Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Setoids.Setoid.
Require Export Coq.Unicode.Utf8.
Require Export CpdtTactics.
Require Export FunctionalExtensionality.

Close Scope nat_scope.
Open Scope program_scope.

Hint Unfold id.
Hint Unfold compose.

Set Primitive Projection.

Axiom propositional_extensionality : forall P : Prop, P -> P = True.
Axiom propositional_extensionality_rev : forall P : Prop, P = True -> P.
Axiom proof_irrelevance : forall (P : Prop) (u v : P), u = v.

Definition π1 {A : Type} {P : A → Type} (k : {x : A & P x}) := projT1 k.
Definition π2 {A : Type} {P : A → Type} (k : {x : A & P x}) := projT2 k.

(* Commonly occurring patterns that can now be solved with 'auto'. *)
Hint Extern 4 (?A = ?A) => reflexivity.
Hint Extern 7 (?X = ?Z) => match goal
  with [H : ?X = ?Y, H' : ?Y = ?Z |- ?X = ?Z] => transitivity Y end.

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
