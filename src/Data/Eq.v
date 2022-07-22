Generalizable All Variables.
Set Primitive Projections.

Class Eq (A : Type) := {
  eqb  : A -> A -> bool;
  neqb : A -> A -> bool;

  eqb_refl x : eqb x x = true;
  eqb_sym x y : eqb x y = eqb y x;
  eqb_trans {x y z} : eqb x y = true -> eqb y z = true -> eqb x z = true;

  eqb_eq {x y} : eqb x y = true -> x = y;
}.

Infix "==" := eqb (at level 70).
Infix "/=" := neqb (at level 70).

Lemma eqb_neq `{Eq A} {x y} : eqb x y = false -> x <> y.
Proof.
  repeat intro; subst.
  pose proof (eqb_refl y).
  rewrite H0 in H1.
  inversion H1.
Qed.
