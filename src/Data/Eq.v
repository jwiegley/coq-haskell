Require Import Hask.Ltac.

Generalizable All Variables.

Class Eq (A : Type) := {
  eqb  : A -> A -> bool;
  neqb : A -> A -> bool
}.

Infix "==" := eqb (at level 70).
Infix "/=" := neqb (at level 70).
