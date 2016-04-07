(* Copyright (c) 2014, John Wiegley
 *
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(** %\chapter{Category}% *)

Require Import Hask.Ltac.
Require Import Hask.Crush.
Require Import Coq.Unicode.Utf8.
Require Import FunctionalExtensionality.
Require Export Coq.Classes.Morphisms.
Export Coq.Classes.Morphisms.ProperNotations.
Require Export Coq.Classes.SetoidClass.

Generalizable All Variables.

Open Scope signature.

(* Set Universe Polymorphism. *)
Generalizable All Variables.

(** * Category *)

(** Category theory is a language for reasoning about abstractions.
Awodey%\cite{Awodey}% calls it, "the algebra of abstract functions."  Its
power lies in relating ideas from differing disciplines, and unifying them
under a common framework.

At its heart we have the [Category].  Every category is characterized by
its objects, and the morphisms (also called arrows) between those
objects. *)

Class Arrows (A : Type) : Type := {
  (* These require Coq 8.5 and universe polymorphism. *)
  (* uhom := Type : Type; *)
  (* Hom  : A → A → uhom where "a ~> b" := (Hom a b); *)
  Hom : A -> A -> Type
}.
Infix "~>" := Hom (at level 70, right associativity).

Coercion Hom : Arrows >-> Funclass.

Instance Opp_Arrows `{Arr : Arrows X} : @Arrows X := {
  Hom := fun A B => @Hom X Arr B A
}.

Instance Fun_Arrows : @Arrows Type := {
  Hom := fun A B => A -> B
}.

Reserved Notation "f ∘ g" (at level 40, left associativity).
Reserved Notation "C ^op" (at level 90).
(* end hide *)

Class Category (Obj : Type) `{Arr : Arrows Obj} := {
  arrows_setoid :> forall x y, Setoid (x ~> y);

  id : ∀ {A}, A ~> A;
  comp : ∀ {A B C}, (B ~> C) → (A ~> B) → (A ~> C)
    where "f ∘ g" := (comp f g);

  right_id : ∀ A B (f : A ~> B), f ∘ id == f;
  left_id : ∀ A B (f : A ~> B), id ∘ f == f;

  comp_proper :> ∀ a b c,
    Proper (equiv ==> equiv ==> equiv) (@comp a b c);
  comp_assoc : ∀ A B C D (f : C ~> D) (g : B ~> C) (h : A ~> B),
    f ∘ (g ∘ h) == (f ∘ g) ∘ h
}.

Infix "~{ C }~>" := (@Hom _ C) (at level 100) : category_scope.
Infix "∘"        := comp (at level 40, left associativity) : category_scope.

Notation "id/ X" := (@id _ _ _ X) (at level 1) : category_scope.

Open Scope category_scope.

(*
Axiom proof_irrelevance : forall (P : Prop) (u v : P), u = v.

Lemma cat_irrelevance `(C : Category) `(D : Category)
  : ∀ (m n : ∀ {A}, A ~> A)
      (p q : ∀ {A B C}, (B ~> C) → (A ~> B) → (A ~> C))
      l l' r r' c c',
  @m = @n →
  @p = @q →
  {| ob           := C
   ; hom          := @hom C
   ; c_id         := @m
   ; c_comp       := @p
   ; c_left_id    := l
   ; c_right_id   := r
   ; c_comp_assoc := c
 |} =
  {| ob           := C
   ; hom          := @hom C
   ; c_id         := @n
   ; c_comp       := @q
   ; c_left_id    := l'
   ; c_right_id   := r'
   ; c_comp_assoc := c'
 |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.
*)

Hint Extern 1 => apply left_id.
Hint Extern 1 => apply right_id.

Hint Extern 4 (?A = ?A) => reflexivity.
Hint Extern 7 (?X = ?Z) =>
  match goal with
    [H : ?X = ?Y, H' : ?Y = ?Z |- ?X = ?Z] => transitivity Y
  end.

Section Morphisms.

Context `{Category C}.

Definition Idempotent `(f : X ~> X) := f ∘ f == f.
Definition Involutive `(f : X ~> X) := f ∘ f == id.

Definition Section'   `(f : X ~> Y) := { g : Y ~> X & g ∘ f == id }.
Definition Retraction `(f : X ~> Y) := { g : Y ~> X & f ∘ g == id }.

Class SplitIdempotent {X Y : C} := {
  split_idem_retract := Y;

  split_idem       : X ~> X;
  split_idem_r     : X ~> split_idem_retract;
  split_idem_s     : split_idem_retract ~> X;
  split_idem_law_1 : split_idem_s ∘ split_idem_r == split_idem;
  split_idem_law_2 : split_idem_r ∘ split_idem_s == id
}.

Definition Epic  `(f : X ~> Y) := ∀ {Z} (g1 g2 : Y ~> Z),
  g1 ∘ f == g2 ∘ f → g1 == g2.
Definition Monic `(f : X ~> Y) := ∀ {Z} (g1 g2 : Z ~> X),
  f ∘ g1 == f ∘ g2 → g1 == g2.

Definition Bimorphic `(f : X ~> Y) := Epic f ∧ Monic f.
Definition SplitEpi  `(f : X ~> Y) := Retraction f.
Definition SplitMono `(f : X ~> Y) := Section' f.

Hint Unfold Idempotent.
Hint Unfold Involutive.
Hint Unfold Section'.
Hint Unfold Retraction.
Hint Unfold Epic.
Hint Unfold Monic.
Hint Unfold Bimorphic.
Hint Unfold SplitEpi.
Hint Unfold SplitMono.

Lemma id_idempotent : ∀ X, Idempotent (id (A := X)).
Proof. auto. Qed.

Lemma id_involutive : ∀ X, Involutive (id (A := X)).
Proof. auto. Qed.

Section Lemmas.

Variables X Y : C.
Variable f : X ~> Y.

Lemma retractions_are_epic : Retraction f → Epic f.
Proof.
  autounfold.
  intros.
  destruct X0.
  rewrite <- right_id.
  symmetry.
  rewrite <- right_id.
  rewrite <- e.
  repeat (rewrite comp_assoc); try f_equiv; auto.
  symmetry.
  exact H0.
Qed.

Lemma sections_are_monic : Section' f → Monic f.
Proof.
  autounfold.
  intros.
  destruct X0.
  rewrite <- left_id.
  symmetry.
  rewrite <- left_id.
  rewrite <- e.
  repeat (rewrite <- comp_assoc); try f_equiv; auto.
  symmetry.
  exact H0.
Qed.

End Lemmas.
End Morphisms.

Definition epi_compose `{Category C} {X Y Z : C}
  `(ef : @Epic C _ _ Y Z f) `(eg : @Epic C _ _ X Y g) : Epic (f ∘ g).
Proof.
  unfold Epic in *. intros.
  apply ef.
  apply eg.
  repeat (rewrite <- comp_assoc); auto.
Qed.

Definition monicompose `{Category C} {X Y Z : C}
  `(ef : @Monic C _ _ Y Z f) `(eg : @Monic C _ _ X Y g) : Monic (f ∘ g).
Proof.
  unfold Monic in *. intros.
  apply eg.
  apply ef.
  repeat (rewrite comp_assoc); auto.
Qed.

(** * Isomorphism

An isomorphism is a pair of mappings that establish an equivalence between
objects.  Using the language above, it is a pair of functions which are both
sections and retractions of one another.  That is, they compose to identity in
both directions:

*)

Class Isomorphism `{Category C} (X Y : C) := {
  to       : X ~> Y;
  from     : Y ~> X;
  iso_to   : to ∘ from == id/Y;
  iso_from : from ∘ to == id/X
}.

(*
Lemma iso_irrelevance `(Category C) {X Y : C}
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
*)

(*
Program Instance iso_identity `{C : Category} (X : C) : X {≅} X := {
    to   := id/X;
    from := id/X
}.

Program Instance iso_symmetry `{C : Category} `(iso : X {≅} Y) : Y {≅} X := {
    to   := @from C X Y iso;
    from := @to C X Y iso
}.
(* begin hide *)
Obligation 1. apply iso_from. Qed.
Obligation 2. apply iso_to. Qed.
(* end hide *)

Program Instance iso_compose `{C : Category} {X Y Z : C}
    (iso_a : Y {≅} Z) (iso_b : X {≅} Y) : X {≅} Z := {
    to   := (@to C Y Z iso_a) ∘ (@to C X Y iso_b);
    from := (@from C X Y iso_b) ∘ (@from C Y Z iso_a)
}.
(* begin hide *)
Obligation 1.
  destruct iso_a.
  destruct iso_b. simpl.
  rewrite <- comp_assoc.
  rewrite (comp_assoc _ _ _ _ to1).
  rewrite iso_to1.
  rewrite left_id.
  assumption.
Qed.
Obligation 2.
  destruct iso_a.
  destruct iso_b. simpl.
  rewrite <- comp_assoc.
  rewrite (comp_assoc _ _ _ _ from0).
  rewrite iso_from0.
  rewrite left_id.
  assumption.
Qed.
(* end hide *)

(*
Definition iso_equiv `{C : Category} {a b : C} (x y : a ≅ b) : Prop :=
  match x with
  | Build_Isomorphism to0 from0 _ _ => match y with
    | Build_Isomorphism to1 from1 _ _ =>
      to0 = to1 ∧ from0 = from1
    end
  end.

Program Instance iso_equivalence `{C : Category} (a b : C)
  : Equivalence (@iso_equiv C a b).
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

Add Parametric Relation `(C : Category) (a b : C) : (a ≅ b) (@iso_equiv C a b)
  reflexivity proved by  (@Equivalence_Reflexive  _ _ (iso_equivalence a b))
  symmetry proved by     (@Equivalence_Symmetric  _ _ (iso_equivalence a b))
  transitivity proved by (@Equivalence_Transitive _ _ (iso_equivalence a b))
    as parametric_relation_iso_eqv.

  Add Parametric Morphism `(C : Category) (a b c : C) : (@iso_compose C a b c)
    with signature (iso_equiv ==> iso_equiv ==> iso_equiv)
      as parametric_morphism_iso_comp.
    intros. unfold iso_equiv, iso_compose.
    destruct x. destruct y. destruct x0. destruct y0.
    simpl in *.
    inversion H. inversion H0.
    split; crush.
Defined.
*)
*)

(*
Program Instance Groupoid `(Category C) : Category C := {
    hom   := @Isomorphism C;
    id    := @iso_identity C
}.
Obligation 1.
  unfold iso_compose, iso_identity.
  destruct f. simpl in *.
  apply iso_irrelevance.
  apply right_id.
  apply left_id.
Qed.
Obligation 2.
  unfold iso_compose, iso_identity.
  destruct f. simpl in *.
  apply iso_irrelevance.
  apply left_id.
  apply right_id.
Qed.
Obligation 3.
  unfold iso_compose.
  destruct f. destruct g. destruct h.
  simpl; apply iso_irrelevance;
  rewrite comp_assoc; reflexivity.
Qed.
*)

(*
Program Instance Monic_Retraction_Iso `{C : Category}
  `(f : X ~{C}~> Y) (r : Retraction f) (m : Monic f) : X {≅} Y := {
  to   := f;
  from := projT1 r
}.
(* begin hide *)
Obligation 1.
  autounfold in *.
  destruct r.
  auto.
Qed.
Obligation 2.
  autounfold in *.
  destruct r.
  simpl.
  specialize (m X (x ∘ f) id).
  apply m.
  rewrite comp_assoc.
  rewrite e.
  auto.
  rewrite left_id.
  rewrite right_id.
  reflexivity.
Qed.
(* end hide *)

Program Instance Epic_Section_Iso
    `{C : Category} {X Y} `(s : Section' f) `(e : Epic f) : X {≅} Y := {
    to   := f;
    from := projT1 s
}.
(* begin hide *)
Obligation 1.
  autounfold in *.
  destruct s.
  simpl.
  specialize (e Y (f ∘ x) id).
  apply e.
  rewrite <- comp_assoc.
  rewrite e0.
  rewrite left_id.
  rewrite right_id.
  reflexivity.
Qed.
Obligation 2.
  autounfold in *.
  destruct s.
  specialize (e Y (f ∘ x) id).
  auto.
Qed.

Hint Unfold Idempotent.
Hint Unfold Involutive.
Hint Unfold Section'.
Hint Unfold Retraction.
Hint Unfold Epic.
Hint Unfold Monic.
Hint Unfold Bimorphic.
Hint Unfold SplitEpi.
Hint Unfold SplitMono.
(* end hide *)

(**

A section may be flipped using its witness to provide a retraction, and
vice-versa.

*)

Definition flip_section `{Category} `(f : X ~> Y)
  (s : @Section' _ X Y f) : @Retraction _ Y X (projT1 s).
Proof.
  autounfold.
  destruct s.
  exists f.
  crush.
Qed.

Definition flip_retraction `{Category} `(f : X ~> Y)
  (s : @Retraction _ X Y f) : @Section' _ Y X (projT1 s).
Proof.
  autounfold.
  destruct s.
  exists f.
  crush.
Qed.
*)

Program Instance Coq : Category Type (Arr:=Fun_Arrows) := {
  id   := fun _ x => x;
  comp := fun _ _ _ f g x => f (g x)
}.
Next Obligation.
  (* Equivalence of arrows in the hom-setoids for this category is given by
     functional extensionality. *)
  refine {| equiv := fun f g => forall x, f x = g x |}.
  constructor; repeat intro.
  - reflexivity.
  - symmetry; apply H.
  - transitivity (y0 x1); [ apply H | apply H0 ].
Defined.
Next Obligation.
  intros f f' Hf g g' Hg x.
  rewrite Hf, Hg; reflexivity.
Qed.

Inductive Objects := obj {
  carrier   :> Type;
  is_setoid :> Setoid carrier
}.

Arguments is_setoid {o}.

Record SetoidMorphism `{Setoid A} `{Setoid B} := {
  morph :> A -> B;
  proper_morph :> Proper (equiv ==> equiv) morph
}.

Program Instance Arrows_Setoid : Arrows Objects := {
  Hom := fun A B => @SetoidMorphism (carrier A) is_setoid
                                    (carrier B) is_setoid
}.

Program Instance Arr_Setoid : forall {A B : Objects}, Setoid (A ~> B) := {
  equiv := fun f g => forall x, @equiv B is_setoid (f x) (g x)
}.
Obligation 1.
  constructor;
  repeat intro;
  [ reflexivity
  | symmetry
  | transitivity (y x0) ];
  eauto.
Qed.

Program Instance SetoidCoq : Category Objects (Arr:=Arrows_Setoid) := {
  id   := fun A : Objects =>
            {| morph := fun x => x
             ; proper_morph := fun _ _ H => H |};
  comp := fun (A B C : Objects) (g : B ~> C) (f : A ~> B) =>
            {| morph := fun x => morph g (morph f x)
             ; proper_morph := fun x y H =>
                 proper_morph g (f x) (f y) (proper_morph f x y H) |}
}.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation.
  intros ?? Hf ?? Hg x.
  simpl.
  rewrite Hf.
  apply proper_morph.
  exact (Hg x).
Qed.
Next Obligation. reflexivity. Qed.

(*
Notation "X ≅Sets Y" :=
  (@Isomorphism Sets X Y) (at level 70, right associativity) : category_scope.
*)

Definition objType `{Category C} := C.
Arguments objType {C Arr} H.

Definition arrType `{@Category C Arr} := Arr.
Arguments arrType {C Arr} H.

Coercion objType : Category >-> Sortclass.
Coercion arrType : Category >-> Arrows.

Section InjSurj.

Variable X : Coq.
Variable Y : Coq.
Context `{Setoid X}.
Context `{Setoid Y}.
Variable f : X ~> Y.

Definition Injective:= ∀ x y, f x == f y → x == y.

(*
Lemma injectivity_is_monic : Injective ↔ Monic f.
Proof.
  unfold Monic, Injective.
  split; intros; simpl in *.
  - intro z.
    apply H. apply (equal_f H0).
  - pose (fun (_ : unit) => x) as const_x.
    pose (fun (_ : unit) => y) as const_y.
    specialize (H unit const_x const_y).
    unfold const_x in H.
    unfold const_y in H.
    apply equal_f in H.
    + assumption.
    + extensionality tt. assumption.
    + constructor.
Qed.
*)

Definition Surjective := ∀ y, ∃ x, f x = y.

Axiom propositional_extensionality : forall P : Prop, P -> P = True.

(*
Lemma surjectivity_is_epic : Surjective ↔ Epic f.
Proof.
  unfold Epic, Surjective.
  split; intros; simpl in *.
  - intro y.
    specialize (H1 y).
    destruct H1.
    rewrite <- H1.
    apply H2.
  - specialize (H1 Prop).
    specialize H with (g1 := fun y0 => ∃ x0, f x0 = y0).
    specialize H with (g2 := fun y  => True).
    eapply equal_f in H.
    erewrite H. constructor.
    extensionality x.
    apply propositional_extensionality.
    exists x. reflexivity.
Qed.
*)

End InjSurj.

Program Instance Opposite `{Category C} :
  Category C (Arr:=@Opp_Arrows C Arr) := {
  id   := fun X : C => @id C Arr H X;
  comp := fun (X Y Z : C) (g : Y ~> Z) (f : X ~> Y) =>
            @comp C Arr H Z Y X f g
}.
Next Obligation. apply arrows_setoid. Defined.
Next Obligation.
  intros f f' Hf g g' Hg.
  rewrite Hf, Hg.
  reflexivity.
Defined.
Next Obligation.
  rewrite comp_assoc.
  reflexivity.
Defined.

(* begin hide *)
Notation "C ^op" := (@Opposite C _ _) (at level 90) : category_scope.
(* end hide *)

Lemma Opp_Arrows_inv `{@Category C Arr} :
  Arr = @Opp_Arrows C (@Opp_Arrows C Arr).
Proof.
  unfold Opp_Arrows. simpl.
  destruct Arr; simpl.
  f_equal.
Defined.

Import EqNotations.

Require Import Coq.Program.Equality.

Lemma op_involutive `{H : Category C} : (H^op)^op = rew Opp_Arrows_inv in H.
Proof.
  unfold eq_rect.
  destruct H. simpl.
Admitted.

(**

Using the functions [op] and [unop], we can "flip" a particular morphism by
mapping to its corresponding morphism in the dual category.

*)

Definition op `{C : Category} : ∀ {X Y : C}, (X ~{C^op}~> Y) → (Y ~{C}~> X).
Proof. auto. Defined.

Definition unop `{C : Category} : ∀ {X Y}, (Y ~{C}~> X) → (X ~{C^op}~> Y).
Proof. auto. Defined.
