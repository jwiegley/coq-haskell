Require Export Basics.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Setoids.Setoid.
Require Export Coq.Relations.Relation_Definitions.

Generalizable All Variables.

Class Isomorphism X Y :=
{ to   : X -> Y
; from : Y -> X

; iso_to   : from ∘ to = id
; iso_from : to ∘ from = id
}.
  Arguments to       {X} {Y} {Isomorphism} _.
  Arguments from     {X} {Y} {Isomorphism} _.
  Arguments iso_to   {X} {Y} {Isomorphism}.
  Arguments iso_from {X} {Y} {Isomorphism}.

Hint Resolve iso_to.
Hint Resolve iso_from.

Notation "X ≅ Y" := (Isomorphism X Y) (at level 50) : type_scope.
Notation "x ≡ y" := (to x = y /\ from y = x) (at level 50).

Section Isos.

  Variables X Y : Type.
  Context `{X ≅ Y}.

  Theorem iso_from_x : forall (y : Y), to (from y) = y.
  Proof.
    intros.
    destruct H.
    simpl.
    rewrite <- uncompose with (f := to0).
      rewrite iso_from0.
      reflexivity.
    assumption.
  Qed.

  Theorem exchange_from : forall (x : X) (y : Y),
    x ≡ y -> from y = x.
  Proof.
    intros.
    destruct H0.
    assumption.
  Qed.

  Theorem exchange_to : forall (x : X) (y : Y),
    x ≡ y -> to x = y.
  Proof.
    intros.
    destruct H0.
    assumption.
  Qed.

End Isos.

Program Instance iso_identity `{C : Category} : X ≅ X := {
    to   := id;
    from := id
}.

Program Instance iso_symmetry `{C : Category} `(iso : X ≅ Y) : Y ≅ X := {
    to   := @from X Y iso;
    from := @to X Y iso
}.

Program Instance iso_compose {X Y Z}
    (iso_a : Y ≅ Z) (iso_b : X ≅ Y) : X ≅ Z := {
    to   := (@to Y Z iso_a) ∘ (@to X Y iso_b);
    from := (@from X Y iso_b) ∘ (@from Y Z iso_a)
}.
(* begin hide *)
Obligation 1.
  destruct iso_a.
  destruct iso_b. simpl.
  rewrite <- comp_assoc.
  rewrite (comp_assoc _ to0).
  rewrite iso_to0.
  rewrite comp_id_left.
  assumption.
Qed.
Obligation 2.
  destruct iso_a.
  destruct iso_b. simpl.
  rewrite <- comp_assoc.
  rewrite (comp_assoc _ from1).
  rewrite iso_from1.
  rewrite comp_id_left.
  assumption.
Qed.
(* end hide *)

Definition iso_equiv {a b} (x y : a ≅ b) : Prop :=
  match x with
  | Build_Isomorphism to0 from0 _ _ => match y with
    | Build_Isomorphism to1 from1 _ _ =>
      to0 = to1 /\ from0 = from1
    end
  end.

Program Instance iso_equivalence (a b : Type)
  : Equivalence (@iso_equiv a b).
Obligation 1.
  unfold Reflexive, iso_equiv. intros.
  destruct x. auto.
Defined.
Obligation 2.
  unfold Symmetric, iso_equiv. intros.
  destruct x. destruct y.
  inversion H.
  split; symmetry; assumption.
Defined.
Obligation 3.
  unfold Transitive, iso_equiv. intros.
  destruct x. destruct y. destruct z.
  inversion H. inversion H0.
  split. transitivity to1; auto.
  transitivity from1; auto.
Defined.

Add Parametric Relation (a b : Type) : (a ≅ b) (@iso_equiv a b)
  reflexivity proved by  (@Equivalence_Reflexive  _ _ (iso_equivalence a b))
  symmetry proved by     (@Equivalence_Symmetric  _ _ (iso_equivalence a b))
  transitivity proved by (@Equivalence_Transitive _ _ (iso_equivalence a b))
    as parametric_relation_iso_eqv.

  Add Parametric Morphism (a b c : Type) : (@iso_compose a b c)
    with signature (iso_equiv ==> iso_equiv ==> iso_equiv)
      as parametric_morphism_iso_comp.
    intros. unfold iso_equiv, iso_compose.
    destruct x. destruct y. destruct x0. destruct y0.
    simpl in *.
    inversion H. inversion H0.
    split; subst; auto.
Defined.
