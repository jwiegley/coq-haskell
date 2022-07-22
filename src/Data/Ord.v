Require Export Hask.Data.Eq.

Generalizable All Variables.

Inductive Ordering := LT | EQ | GT.

Class Ord (A : Type) `{Eq A} := {
  compare : A -> A -> Ordering;
  ltb : A -> A -> bool;
  lteb : A -> A -> bool;
  gtb : A -> A -> bool;
  gteb : A -> A -> bool;
  max : A -> A -> A;
  min : A -> A -> A
}.

Infix "<" := ltb (at level 70).
Infix "<=" := lteb (at level 70).
Infix ">" := gtb (at level 70).
Infix ">=" := gteb (at level 70).
