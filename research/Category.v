(* Copyright (c) 2014, John Wiegley
 *
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(** %\chapter{Category}% *)

Require Export Basics.

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

(* begin hide *)
Reserved Notation "a ~> b" (at level 70, right associativity).
Reserved Notation "f ∘ g" (at level 40, left associativity).
Reserved Notation "C ^op" (at level 90).
(* end hide *)

Class Category := {
    ob   : Type;
    (* These require Coq 8.5 and universe polymorphism. *)
    (* uhom := Type : Type; *)
    (* hom  : ob → ob → uhom where "a ~> b" := (hom a b); *)
    hom  : ob → ob → Type where "a ~> b" := (hom a b);
(**

It is important to note that objects and arrows have no inherent meaning: The
notion of a category requires only that they exist, and that they be
well-behaved.  Since all we can know about objects is that they exist, they
serve only to differentiate morphisms.  Conversely, morphisms are how we
characterize objects. *)

(** * Morphisms

In this formalization, as in many textbooks, morphisms are called [hom], for
"homomorphism" (algebraic structure-preserving maps).  Each morphism
represents the set of all morphism having that type, so they are also called
"hom-sets".

Since categories may have other categories as objects, we require that the
type of [hom] be larger than the type of its arguments.  This is the purpose
of the [uhom] type, allowing us to make use of Coq's support for universe
polymorphism.

*)

    id : ∀ {A}, A ~> A;
    compose : ∀ {A B C}, (B ~> C) → (A ~> B) → (A ~> C) where "f ∘ g" := (compose f g);
(**

If [ob] and [hom] are the nouns of category theory, [id] and [compose] are its
fundamental verbs.  Using only these notions we can reason about concepts such
as _idempotency_, _involution_, _section_ and _retraction_, _equalizers_ and
_co-equalizers_, and more.  Before we may do so, however, we must constrain
identity and composition under three laws:

*)

    right_identity : ∀ A B (f : A ~> B), f ∘ id = f;
    left_identity : ∀ A B (f : A ~> B), id ∘ f = f;
    comp_assoc : ∀ A B C D (f : C ~> D) (g : B ~> C) (h : A ~> B),
        f ∘ (g ∘ h) = (f ∘ g) ∘ h
}.

(**

Note the difference between the arrow used for function types in Coq, such as
[A → B], and for morphisms in a category [A ~> B].  If the category must be
indicated, it is stated in the arrow: [A ~{C}~> B]. *)

(* begin hide *)
(* Using a [Category] in a context requiring a [Type] will do what is expected
   using this coercion. *)
Coercion ob : Category >-> Sortclass.
(* Coercion hom : Category >-> Funclass. *)

Infix "~>"       := hom : category_scope.
Infix "~{ C }~>" := (@hom C) (at level 100) : category_scope.
Infix "∘"        := compose (at level 40, left associativity) : category_scope.

Notation "ob/ C" := (@ob C) (at level 1) : category_scope.
Notation "id/ X" := (@id _ X) (at level 1) : category_scope.

Open Scope category_scope.

Lemma cat_irrelevance `(C : Category) `(D : Category)
  : ∀ (m n : ∀ {A}, A ~> A)
      (p q : ∀ {A B C}, (B ~> C) → (A ~> B) → (A ~> C))
      l l' r r' c c',
  @m = @n →
  @p = @q →
  {| ob              := C
   ; hom             := @hom C
   ; id              := @m
   ; compose         := @p
   ; left_identity   := l
   ; right_identity  := r
   ; comp_assoc      := c
 |} =
  {| ob              := C
   ; hom             := @hom C
   ; id              := @n
   ; compose         := @q
   ; left_identity   := l'
   ; right_identity  := r'
   ; comp_assoc      := c'
 |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.

Hint Extern 1 => apply left_identity.
Hint Extern 1 => apply right_identity.

Hint Extern 4 (?A = ?A) => reflexivity.
Hint Extern 7 (?X = ?Z) =>
  match goal with
    [H : ?X = ?Y, H' : ?Y = ?Z |- ?X = ?Z] => transitivity Y
  end.

(* end hide *)

(**

We may now extend our discourse about functions, using only the few terms
we've defined so far:

*)

(* begin hide *)
Section Morphisms.
Context `{C : Category}.
(* end hide *)

Definition Idempotent `(f : X ~> X) := f ∘ f = f.
Definition Involutive `(f : X ~> X) := f ∘ f = id.

(**

We can also define relationships between two functions:

*)

Definition Section'   `(f : X ~> Y) := { g : Y ~> X & g ∘ f = id }.
Definition Retraction `(f : X ~> Y) := { g : Y ~> X & f ∘ g = id }.

Class SplitIdempotent {X Y : C} := {
    split_idem_retract := Y;

    split_idem       : X ~> X;
    split_idem_r     : X ~> split_idem_retract;
    split_idem_s     : split_idem_retract ~> X;
    split_idem_law_1 : split_idem_s ∘ split_idem_r = split_idem;
    split_idem_law_2 : split_idem_r ∘ split_idem_s = id/Y
}.

(**

A Σ-type (sigma type) is used to convey [Section'] and [Retraction] to make
the witness available to proofs.  The definition could be expressed with an
existential quantifier (∃), but it would not convey which [g] was chosen.

*)

Definition Epic  `(f : X ~> Y) := ∀ {Z} (g1 g2 : Y ~> Z), g1 ∘ f = g2 ∘ f → g1 = g2.
Definition Monic `(f : X ~> Y) := ∀ {Z} (g1 g2 : Z ~> X), f ∘ g1 = f ∘ g2 → g1 = g2.

Definition Bimorphic `(f : X ~> Y) := Epic f ∧ Monic f.
Definition SplitEpi  `(f : X ~> Y) := Retraction f.
Definition SplitMono `(f : X ~> Y) := Section' f.

(**

The only morphism we've seen so far is [id], but we can trivially prove it is
both _idempotent_ and _involutive_. *)

(* begin hide *)
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

Lemma id_idempotent : ∀ X, Idempotent (id (A := X)).
Proof. auto. Qed.

Lemma id_involutive : ∀ X, Involutive (id (A := X)).
Proof. auto. Qed.

(**

We can also prove some relationships among these definitions. *)

(* begin hide *)
Section Lemmas.
Variables X Y : C.
Variable f : X ~> Y.
(* end hide *)

Lemma retractions_are_epic : Retraction f → Epic f.
Proof.
  autounfold.
  intros.
  destruct X0.
  rewrite <- right_identity.
  symmetry.
  rewrite <- right_identity.
  rewrite <- e.
  repeat (rewrite comp_assoc); try f_equal; auto.
Qed.

Lemma sections_are_monic : Section' f → Monic f.
Proof.
  autounfold.
  intros.
  destruct X0.
  rewrite <- left_identity.
  symmetry.
  rewrite <- left_identity.
  rewrite <- e.
  repeat (rewrite <- comp_assoc); try f_equal; auto.
Qed.

(* begin hide *)
End Lemmas.
End Morphisms.
(* end hide *)

Definition epi_compose `{C : Category} {X Y Z : C}
  `(ef : @Epic C Y Z f) `(eg : @Epic C X Y g) : Epic (f ∘ g).
Proof.
  unfold Epic in *. intros.
  apply ef.
  apply eg.
  repeat (rewrite <- comp_assoc); auto.
Qed.

Definition monic_compose `{C : Category} {X Y Z : C}
  `(ef : @Monic C Y Z f) `(eg : @Monic C X Y g) : Monic (f ∘ g).
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

Class Isomorphism `{C : Category} (X Y : C) := {
  to       : X ~> Y;
  from     : Y ~> X;
  iso_to   : to ∘ from = id/Y;
  iso_from : from ∘ to = id/X
}.

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

(**

Typically isomorphisms are characterized by this pair of functions, but they
can also be expressed as an equivalence between objects using the notation [A
≅ B].  A double-tilde is used to express the same notion of equivalence
between value terms [a = b].

*)

Notation "X ≅ Y" := (Isomorphism X Y) (at level 70, right associativity) : category_scope.
Notation "x ≡ y" := (to x = y ∧ from y = x) (at level 70, right associativity).

(**

[id] witnesses the isomorphism between any object and itself.  Isomorphisms
are likewise symmetric and transitivity, making them parametric relations.
This will allows us to use them in proof rewriting as though they were
equalities.

*)

Program Instance iso_identity `{C : Category} (X : C) : X ≅ X := {
    to   := id/X;
    from := id/X
}.

Program Instance iso_symmetry `{C : Category} `(iso : X ≅ Y) : Y ≅ X := {
    to   := @from C X Y iso;
    from := @to C X Y iso
}.
(* begin hide *)
Obligation 1. apply iso_from. Qed.
Obligation 2. apply iso_to. Qed.
(* end hide *)

Program Instance iso_compose `{C : Category} {X Y Z : C}
    (iso_a : Y ≅ Z) (iso_b : X ≅ Y) : X ≅ Z := {
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
  rewrite left_identity.
  assumption.
Qed.
Obligation 2.
  destruct iso_a.
  destruct iso_b. simpl.
  rewrite <- comp_assoc.
  rewrite (comp_assoc _ _ _ _ from0).
  rewrite iso_from0.
  rewrite left_identity.
  assumption.
Qed.
(* end hide *)

Definition iso_equiv `{C : Category} {a b : C} (x y : a ≅ b) : Prop :=
  match x with
  | Build_Isomorphism _ _ _ to0 from0 _ _ => match y with
    | Build_Isomorphism _ _ _ to1 from1 _ _ =>
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

(**

A [Groupoid] is a [Category] where every morphism has an inverse, and is
therefore an isomorphism.

*)

Program Instance Groupoid `(C : Category) : Category := {
    ob      := @ob C;
    hom     := @Isomorphism C;
    id      := @iso_identity C
}.
(* begin hide *)
Obligation 1.
  unfold iso_compose, iso_identity.
  destruct f. simpl in *.
  apply iso_irrelevance.
  apply right_identity.
  apply left_identity.
Qed.
Obligation 2.
  unfold iso_compose, iso_identity.
  destruct f. simpl in *.
  apply iso_irrelevance.
  apply left_identity.
  apply right_identity.
Qed.
Obligation 3.
  unfold iso_compose.
  destruct f. destruct g. destruct h.
  simpl; apply iso_irrelevance;
  rewrite comp_assoc; reflexivity.
Qed.
(* end hide *)

(**

A function which is both a retraction and monic, or a section and epic, bears
an isomorphism with its respective witness.

*)

Program Instance Monic_Retraction_Iso
    `{C : Category} `(f : X ~{C}~> Y) (r : Retraction f) (m : Monic f) : X ≅ Y := {
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
  rewrite left_identity.
  rewrite right_identity.
  reflexivity.
Qed.
(* end hide *)

Program Instance Epic_Section_Iso
    `{C : Category} {X Y} `(s : Section' f) `(e : Epic f) : X ≅ Y := {
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
  rewrite left_identity.
  rewrite right_identity.
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

(** * Sets

[Sets] is our first real category: the category of Coq types and functions.
The objects of this category are all the Coq types (including [Set], [Prop]
and [Type]), and its morphisms are functions from [Type] to [Type].  [id]
simply returns whatever object is passed, and [compose] is regular composition
between functions.  Proving it is a category in Coq is automatic.

Note that in many textbooks this category (or one similar to it) is called
just [Set], but since that name conflicts with types of the same name in Coq,
the plural is used instead.

*)

Program Instance Sets : Category := {
    ob      := Type;
    hom     := fun X Y => X → Y;
    id      := fun _ x => x;
    compose := fun _ _ _ f g x => f (g x)
}.
(**

Within the category of [Sets] we can prove that monic functions are injective,
and epic functions are surjective.  This is not necessarily true in other
categories.

*)

Notation "X ≅Sets Y" :=
  (@Isomorphism Sets X Y) (at level 70, right associativity) : category_scope.

Definition Injective `(f : X → Y) := ∀ x y, f x = f y → x = y.

Lemma injectivity_is_monic `(f : X → Y) : Injective f ↔ Monic f.
Proof.
  unfold Monic, Injective.
  split; intros; simpl in *.
  - extensionality z.
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

Definition Surjective `(f : X → Y) := ∀ y, ∃ x, f x = y.

Lemma surjectivity_is_epic `(f : X → Y) : Surjective f ↔ Epic f.
Proof.
  unfold Epic, Surjective.
  split; intros; simpl in *.
  - extensionality y.
    specialize (H y).
    destruct H.
    rewrite <- H.
    apply (equal_f H0).
  - specialize H with (Z := Prop).
    specialize H with (g1 := fun y0 => ∃ x0, f x0 = y0).
    specialize H with (g2 := fun y  => True).
    eapply equal_f in H.
    erewrite H. constructor.
    extensionality x.
    apply propositional_extensionality.
    exists x. reflexivity.
Qed.

(** * Dual Category

The opposite, or dual, of a category is expressed [C^op].  It has the same
objects as its parent, but the direction of all morphisms is flipped.  Doing
this twice should result in the same category, making it an involutive
operation.

*)

Program Instance Opposite `(C : Category) : Category := {
    ob      := @ob C;
    hom     := fun x y => @hom C y x;
    id      := @id C;
    compose := fun _ _ _ f g => g ∘ f
}.
Obligation 3. rewrite comp_assoc. auto. Defined.

(* begin hide *)
Notation "C ^op" := (Opposite C) (at level 90) : category_scope.
(* end hide *)

Lemma op_involutive (C : Category) : (C^op)^op = C.
Proof.
  unfold Opposite.
  unfold Opposite_obligation_1.
  unfold Opposite_obligation_2.
  unfold Opposite_obligation_3.
  simpl. destruct C. simpl.
  apply f_equal3; repeat (extensionality e; simpl; crush).
  extensionality b.
  extensionality c.
  extensionality d.
  extensionality f.
  extensionality g.
  extensionality h. crush.
Qed.

(**

Using the functions [op] and [unop], we can "flip" a particular morphism by
mapping to its corresponding morphism in the dual category.

*)

Definition op `{C : Category} : ∀ {X Y}, (X ~{C^op}~> Y) → (Y ~{C}~> X).
Proof. auto. Defined.

Definition unop `{C : Category} : ∀ {X Y}, (Y ~{C}~> X) → (X ~{C^op}~> Y).
Proof. auto. Defined.
