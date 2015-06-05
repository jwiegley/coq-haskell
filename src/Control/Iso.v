Require Import Hask.Prelude.
Require Import Hask.Control.Monad.

Generalizable All Variables.

Class Isomorphism (A B : Type) : Type := {
    iso_to   : A -> B;
    iso_from : B -> A
}.

Arguments iso_to   {A} {B} {Isomorphism} _.
Arguments iso_from {A} {B} {Isomorphism} _.

Infix "≅" := Isomorphism (at level 30) : type_scope.

Definition Iso (A B : Type) : Prop := inhabited (A ≅ B).

Module IsomorphismLaws.

Class IsomorphismLaws (A B : Type) `{A ≅ B} : Type := {
    iso_to_id   : iso_from \o iso_to =1 id;
    iso_from_id : iso_to \o iso_from =1 id
}.

End IsomorphismLaws.
