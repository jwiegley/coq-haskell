Require Export Basics.
Require Export Endo.
Require Export FCompose.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Setoids.Setoid.
Require Export Coq.Relations.Relation_Definitions.

Generalizable All Variables.

Class Iso (A B : Type) : Type := {
    to   : A -> B;
    from : B -> A;

    iso_to   : from ∘ to = id;
    iso_from : to ∘ from = id
}.

Arguments to       {A} {B} {Iso} _.
Arguments from     {A} {B} {Iso} _.
Arguments iso_to   {A} {B} {Iso}.
Arguments iso_from {A} {B} {Iso}.

Infix "≅" := Iso (at level 50) : type_scope.
(* Notation "x ≡ y" := (to x = y /\ from y = x) (at level 50). *)

Definition Isomorphic (A B : Type) : Prop := inhabited (A ≅ B).

Section Isos.

  Variables A B : Type.
  Context `{A ≅ B}.

  Theorem iso_prop : forall {X} (a : X -> A) (b : X -> B),
    a = from ∘ b <-> to ∘ a = b.
  Proof.
    intros. destruct H. simpl.
    split; intros.
      rewrite <- comp_id_left.
      rewrite <- iso_from0.
      rewrite <- comp_assoc.
      rewrite <- H0.
      reflexivity.
    symmetry.
    rewrite <- comp_id_left.
    rewrite <- iso_to0.
    rewrite <- comp_assoc.
    rewrite <- H0.
    reflexivity.
  Qed.

  Theorem iso_to_x : forall (x : A), from (to x) = x.
  Proof.
    intros. destruct H. simpl.
    rewrite <- uncompose with (f := from0).
      rewrite iso_to0.
      reflexivity.
    assumption.
  Qed.

  Theorem iso_from_x : forall (x : B), to (from x) = x.
  Proof.
    intros. destruct H. simpl.
    rewrite <- uncompose with (f := to0).
      rewrite iso_from0.
      reflexivity.
    assumption.
  Qed.

  Theorem iso_prop_set : forall (a : A) (b : B),
    a = from b <-> to a = b.
  Proof.
    intros.
    split; intros.
      rewrite H0.
      apply iso_from_x.
    symmetry.
    rewrite <- H0.
    apply iso_to_x.
  Qed.

  Theorem iso_prop_x : forall {X} (a : X -> A) (b : X -> B),
    (forall (x : X), a x = from (b x)) <-> (forall (x : X), to (a x) = b x).
  Proof.
    intros. destruct H; simpl.
    assert (forall x, to0 (a x) = (to0 ∘ a) x). auto.
    assert (forall x, from0 (b x) = (from0 ∘ b) x). auto.
    split; intros;
    [ specialize (H0 x); rewrite H0
    | specialize (H1 x); rewrite H1; symmetry ];
    apply equal_f;
    rewrite <- comp_id_left;
    [ rewrite <- iso_from0 | rewrite <- iso_to0 ];
    rewrite <- comp_assoc;
    extensionality y;
    unfold compose;
    rewrite <- H2; auto.
  Qed.

  (* Theorem exchange_from : forall (x : X) (y : Y), *)
  (*   x ≡ y -> from y = x. *)
  (* Proof. intros. destruct H0. assumption. Qed. *)

  (* Theorem exchange_to : forall (x : X) (y : Y), *)
  (*   x ≡ y -> to x = y. *)
  (* Proof. intros. destruct H0. assumption. Qed. *)

End Isos.

Program Instance iso_reflexive : A ≅ A := {
    to   := id;
    from := id
}.

Program Instance iso_symmetry `(iso : A ≅ B) : B ≅ A := {
    to   := @from A B iso;
    from := @to A B iso
}.
Obligation 1. destruct iso. assumption. Qed.
Obligation 2. destruct iso. assumption. Qed.

Program Instance iso_transitivity {A B C}
    (iso_a : B ≅ C) (iso_b : A ≅ B) : A ≅ C := {
    to   := (@to B C iso_a) ∘ (@to A B iso_b);
    from := (@from A B iso_b) ∘ (@from B C iso_a)
}.
(* begin hide *)
Obligation 1.
  destruct iso_a.
  destruct iso_b. simpl.
  rewrite <- comp_assoc.
  rewrite (comp_assoc _ to0).
  rewrite iso_to0.
  assumption.
Qed.
Obligation 2.
  destruct iso_a.
  destruct iso_b. simpl.
  rewrite <- comp_assoc.
  rewrite (comp_assoc _ from1).
  rewrite iso_from1.
  assumption.
Qed.
(* end hide *)

Definition Natural_Iso `(Functor F) `(Functor G) := forall {X}, F X ≅ G X.

Notation "F  [≅]  G" := (Natural_Iso F G) (at level 50) : type_scope.

Program Instance Functor_Congruence `{A ≅ B} `(Functor F) : F A ≅ F B := {
    to   := fmap to;
    from := fmap from
}.
Next Obligation. (* fun_identity *)
  intros.
  rewrite fun_composition.
  rewrite iso_to.
  apply fun_identity.
Defined.
Next Obligation. (* fun_composition *)
  intros.
  rewrite fun_composition.
  rewrite iso_from.
  apply fun_identity.
Defined.

Lemma iso_functor_impl `(iso : A ≅ B) `(F : Functor) `(G : Functor)
  (T : F [≅] G) : F A ≅ G B.
Proof.
  apply (iso_transitivity (T B) (@Functor_Congruence A B iso F _)).
Qed.

Lemma iso_functor_compose
  `{F1 : Functor} `{F2 : Functor} `{G1 : Functor} `{G2 : Functor}
  (HF : F1 [≅] F2) (HG : G1 [≅] G2) : F1 ◌ G1 [≅] F2 ◌ G2.
Proof.
  intros. unfold Natural_Iso in *.
  intros. apply iso_functor_impl; auto.
Qed.

Program Instance FullyFaithful_Iso `(FullyFaithful F)
  : forall A B, (A -> B) ≅ (F A -> F B).
Obligation 1.
  apply fmap with (X := A); assumption.
Defined.
Obligation 2.
  destruct H.
  destruct is_full.
  apply (unfmap A); assumption.
Defined.
Obligation 3.
  unfold FullyFaithful_Iso_obligation_1.
  unfold FullyFaithful_Iso_obligation_2.
  unfold compose.
  destruct H.
  destruct is_full.
  extensionality f.
  destruct is_faithful.
  extensionality x.
  rewrite (faithful_prop A B (unfmap A B (λ X0 : F A, (fmap[F] f) X0)) f).
    reflexivity.
  pose (full_prop _ _ (fmap[F] (unfmap A B (λ X0 : F A, (fmap[F] f) X0)))).
  rewrite e with (f0 := f).
  destruct F0. reflexivity.
Defined.
Obligation 4.
  unfold FullyFaithful_Iso_obligation_1.
  unfold FullyFaithful_Iso_obligation_2.
  unfold compose.
  extensionality f.
  extensionality x.
  destruct F0.
  destruct H.
  destruct is_full.
  erewrite <- full_prop.
  reflexivity.
Defined.

Program Instance Functor_Reflection `{FullyFaithful F} `(F A ≅ F B)
  : A ≅ B := {
    to   := unfmap to;
    from := unfmap from
}.
Obligation 1.
  intros.
  destruct F0.
  destruct H.
  destruct is_full.
  destruct is_faithful.
  apply faithful_prop.
  apply full_prop.
Defined.
Obligation 2.
  intros.
  destruct F0.
  destruct H.
  destruct is_full.
  destruct is_faithful.
  apply faithful_prop.
  apply full_prop.
Defined.

(* Definition Functor_Equivalence `(FullyFaithful F) {A B} := *)
(*   A ≅ B <-> F A ≅ F B. *)

Lemma functor_compose_equiv
  `{FF : FullyFaithful F} `(G : Functor) `(H : Functor)
  (T : G [≅] H) : F ◌ G [≅] F ◌ H.
Proof.
  intros. unfold Natural_Iso in *. intros.
  apply Functor_Congruence.
  assumption.
Qed.

Program Instance Yoneda `(F : Functor) {A}
  : (Hom A ⟾ F) ≅ F A := {
    to   := fun f => transport id;
    from := fun x => {| transport := fun _ f => fmap f x |}
}.
Obligation 1.
  unfold compose.
  extensionality x0.
  rewrite fun_composition_x.
  reflexivity.
Qed.
Obligation 2.
  extensionality k.
  unfold compose, id.
  destruct k.
  simpl in *.
  apply nat_irrelevance.
  extensionality H.
  extensionality f.
  specialize (naturality A H f).
  apply (equal_f naturality).
Defined.
Obligation 3.
  extensionality k.
  unfold compose.
  unfold id at 2.
  apply fun_identity_x.
Defined.

(*
Definition CPS_Yoneda A B : (forall {X}, (B -> X) -> (A -> X)) ≅ (A -> B) :=
  Yoneda (Hom A).
*)

Definition Indirect_Isomorphism_1 `(H : A ≅ B) {X} : Hom A X ≅ Hom B X.
Proof.
Admitted.

Definition Indirect_Isomorphism_2 `(H : Hom A [≅] Hom B) : A ≅ B.
Proof.
Admitted.

Definition Indirect_Isomorphism_3 `(H : A ≅ B) {X} : Hom X A ≅ Hom X B :=
  Functor_Congruence (Hom X).

Definition Indirect_Isomorphism_4 {X} `(H : Hom X A ≅ Hom X B) : A ≅ B :=
  Functor_Reflection H.

Definition Yoneda_spec2 `{F : Functor} `{G : Functor} `(H : F [≅] G) {X}
  : Hom X ◌ F [≅] Hom X ◌ G.
Proof.
  intros.
  apply functor_compose_equiv.
  assumption.
Defined.

Definition Representable `(F : Functor) := { A : Type & Hom A [≅] F }.

(*
Definition Representable_Nat `(F : Functor) `{Representable F}
  : { A : Type & Hom A ⟾ F }.
Proof.
  destruct Representable0.
  exists x.
  eapply Build_Natural
    with (transport := fun X f => _).
  intros.
  unfold compose. simpl.
  extensionality x0.
  reflexivity.
*)

Lemma representable_unique `(F : Functor)
  : forall A B, Hom A [≅] F -> Hom B [≅] F -> A ≅ B.
Proof.
  intros.
  apply Indirect_Isomorphism_2.
  unfold Natural_Iso in *. intros.
  apply (iso_transitivity (iso_symmetry (X0 X1)) (X X1)).
Qed.

Definition Representational_Coproduct (A A1 A2 : Type) :=
  forall {X}, Hom A X ≅ (Hom A1 X * Hom A2 X).

Program Instance Arith_Zero
  : (forall B : Type, Hom False B) ≅ (forall B : Type, True) := {
    to   := fun _ _ => I
}.
Obligation 1.
  intuition.
  apply hom_irrelevance.
  intros.
  contradiction.
Defined.
Obligation 2.
  unfold Arith_Zero_obligation_1.
  compute.
  extensionality f.
  extensionality B.
  extensionality H.
  contradiction H.
Qed.
Obligation 3.
  unfold Arith_Zero_obligation_1.
  compute.
  extensionality f.
  extensionality B.
  apply proof_irrelevance.
Qed.

Program Instance Arith_One
  : (forall A : Type, Hom A True) ≅ (forall A : Type, True) := {
    to   := fun _ _ => I;
    from := fun _ _ _ => I
}.
Obligation 1.
  compute.
  extensionality f.
  extensionality B.
  extensionality x.
  apply proof_irrelevance.
Qed.
Obligation 2.
  compute.
  extensionality f.
  extensionality B.
  apply proof_irrelevance.
Qed.

Program Instance Arith_Plus (A1 A2 : Type)
  : (forall B : Type, Hom (A1 + A2) B) ≅
    (forall B : Type, (Hom A1 B * Hom A2 B)).
Obligation 1.
  split.
  apply hom_irrelevance. intros.
  apply (@hom_irrelevance_r _ B (X B) (inl X0)).
  apply hom_irrelevance. intros.
  apply (@hom_irrelevance_r _ B (X B) (inr X0)).
Defined.
Obligation 2.
  apply hom_irrelevance. intros.
  destruct X0.
  destruct (X B).
  apply (hom_irrelevance_r B f). auto.
  destruct (X B).
  apply (hom_irrelevance_r B f0). auto.
Defined.
Obligation 3.
  compute.
  extensionality f.
  extensionality B.
  extensionality X0.
  destruct X0; reflexivity.
Qed.
Obligation 4.
  compute.
  extensionality f.
  extensionality B.
  destruct f. auto.
Qed.