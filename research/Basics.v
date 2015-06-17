Require Export FunctionalExtensionality.

Set Primitive Projection.

Axiom propositional_extensionality : forall P : Prop, P -> P = True.
Axiom propositional_extensionality_rev : forall P : Prop, P = True -> P.
Axiom proof_irrelevance : forall (P : Prop) (u v : P), u = v.

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
