Require Import Hask.Ssr.
Require Import Hask.Control.Monad.

Generalizable All Variables.

(** * Isomorphism

An isomorphism is a pair of mappings that establish an equivalence between
objects.  Using the language above, it is a pair of functions which are both
sections and retractions of one another.  That is, they compose to identity in
both directions:

*)

Class Isomorphism (A B : Type) : Type := {
    iso_to   : A -> B;
    iso_from : B -> A
}.

Arguments iso_to   {A} {B} {Isomorphism} _.
Arguments iso_from {A} {B} {Isomorphism} _.

(**

Typically isomorphisms are characterized by this pair of functions, but they
can also be expressed as an equivalence between objects using the notation [A
≅ B].  A double-tilde is used to express the same notion of equivalence
between value terms [a = b].

*)

Infix "≅" := Isomorphism (at level 30) : type_scope.
Notation "x ≡ y" :=
  (iso_to x = y /\ iso_from y = x) (at level 70, right associativity).

Definition Iso (A B : Type) : Prop := inhabited (A ≅ B).

Module IsomorphismLaws.

(*
(* begin hide *)
Lemma iso_irrelevance `(C : Category) {X Y : C}
  : ∀ (f g : X ~> Y) (k h : Y ~> X) tl tl' fl fl',
  @f = @g →
  @k = @h →
  {| to       := f
   ; from     := k
   ; iso_to   := tl
   ; iso_from := fl
  |} =
  {| to       := g
   ; from     := h
   ; iso_to   := tl'
   ; iso_from := fl'
  |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.
(* end hide *)
*)

Class IsomorphismLaws (A B : Type) `{A ≅ B} : Type := {
    iso_to_id   : iso_from \o iso_to =1 id;
    iso_from_id : iso_to \o iso_from =1 id
}.

End IsomorphismLaws.
