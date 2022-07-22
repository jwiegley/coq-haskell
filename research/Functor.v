Require Export Category.

Close Scope nat_scope.
Open Scope category_scope.

Generalizable All Variables.

Class Functor {C : Category} {D : Category} :=
{ fobj : C → D
; fmap : ∀ {X Y : C}, (X ~> Y) → (fobj X ~> fobj Y)

; functor_id_law : ∀ {X : C}, fmap (id (A := X)) = id
; functor_compose_law : ∀ {X Y Z : C} (f : Y ~> Z) (g : X ~> Y),
    fmap f ∘ fmap g = fmap (f ∘ g)
}.

Notation "C ⟶ D" := (@Functor C D) (at level 90, right associativity).

(* Functors used as functions will map objects of categories, similar to the
   way type constructors behave in Haskell. *)
Coercion fobj : Functor >-> Funclass.

(* jww (2014-08-11): Have the ∘ symbol refer to morphisms in any category, so
   that it can be used for both arrows and functors (which are arrows in
   Cat). *)
#[export]
Program Instance fun_compose
  {C : Category} {D : Category} {E : Category}
  (F : D ⟶ E) (G : C ⟶ D) : C ⟶ E := {
    fobj := fun x => fobj (fobj x);
    fmap := fun _ _ f => fmap (fmap f)
}.
Obligation 1.
  rewrite functor_id_law.
  apply functor_id_law.
Defined.
Obligation 2.
  rewrite functor_compose_law.
  rewrite functor_compose_law.
  reflexivity.
Defined.

Lemma fun_irrelevance `(C : Category) `(D : Category)
  : ∀ (a : C → D)
      (f g : ∀ {X Y : C}, (X ~> Y) → (a X ~> a Y))
      i i' c c',
  @f = @g →
  {| fobj := @a
   ; fmap := @f
   ; functor_id_law      := i
   ; functor_compose_law := c |} =
  {| fobj := @a
   ; fmap := @g
   ; functor_id_law      := i'
   ; functor_compose_law := c' |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.

(* The Identity [Functor] *)

Definition Id `{C : Category} : C ⟶ C.
  apply Build_Functor with
    (fobj := fun X => X)
    (fmap := fun X X f => f); crush.
Defined.

Lemma fun_left_identity `(F : C ⟶ D) : fun_compose Id F = F.
Proof.
  destruct F.
  unfold fun_compose.
  apply fun_irrelevance.
  extensionality h.
  extensionality h0.
  extensionality f. crush.
Qed.

Lemma fun_right_identity `(F : C ⟶ D) : fun_compose F Id = F.
Proof.
  destruct F.
  unfold fun_compose.
  apply fun_irrelevance.
  extensionality h.
  extensionality h0.
  extensionality f. crush.
Qed.

(** [Cat] is the category whose morphisms are functors betwen categories.
    jww (2014-08-24): Coq 8.5 with universe polymorphism is needed. *)

(*
Section Hidden.

#[export]
Program Instance Cat : Category :=
{ ob      := Category
; hom     := @Functor
; id      := @Id
; compose := @fun_compose
}.
Obligation 1.
  unfold fun_compose.
  destruct f.
  apply fun_irrelevance.
  extensionality e.
  extensionality f.
  extensionality g.
  reflexivity.
Defined.
Obligation 2.
  unfold fun_compose.
  destruct f.
  apply fun_irrelevance.
  extensionality e.
  extensionality f.
  extensionality g.
  reflexivity.
Defined.
Obligation 3.
  unfold fun_compose.
  destruct f.
  apply fun_irrelevance.
  extensionality e.
  extensionality f.
  reflexivity.
Defined.

#[export]
Program Instance One : Category := {
    ob      := unit;
    hom     := fun _ _ => unit;
    id      := fun _ => tt;
    compose := fun _ _ _ _ _ => tt
}.
Obligation 1. destruct f. reflexivity. Qed.
Obligation 2. destruct f. reflexivity. Qed.

#[export]
Program Instance Fini `(C : Category) : C ⟶ One := {
    fobj    := fun _ => tt;
    fmap    := fun _ _ _ => id
}.

#[export]
Program Instance Zero : Category := {
    ob      := Empty_set;
    hom     := fun _ _ => Empty_set
}.
Obligation 3.
    unfold Zero_obligation_1.
    unfold Zero_obligation_2.
    destruct A.
Defined.

#[export]
Program Instance Init `(C : Category) : Zero ⟶ C.
Obligation 1. destruct C. crush. Defined.
Obligation 2.
  unfold Init_obligation_1.
  destruct C. crush.
Defined.
Obligation 3.
  unfold Zero_obligation_1.
  unfold Init_obligation_1.
  unfold Init_obligation_2.
  destruct C. crush.
Defined.
Obligation 4.
  unfold Init_obligation_2.
  unfold Zero_obligation_2.
  destruct C. crush.
Qed.

Class HasInitial (C : Category) :=
{ init_obj    : C
; init_mor    : ∀ {X}, init_obj ~> X
; initial_law : ∀ {X} (f g : init_obj ~> X), f = g
}.

#[export]
Program Instance Cat_HasInitial : HasInitial Cat := {
    init_obj := Zero;
    init_mor := Init
}.
Obligation 1.
  induction f as [F].
  induction g as [G].
  assert (F = G).
    extensionality e.
    crush.
  replace F with G. subst.
  assert (fmap0 = fmap1).
    extensionality e.
    extensionality f.
    extensionality g.
    crush.
  apply fun_irrelevance.
  assumption.
Qed.

Class HasTerminal (C : Category) :=
{ term_obj     : C
; term_mor     : ∀ {X}, X ~> term_obj
; terminal_law : ∀ {X} (f g : X ~> term_obj), f = g
}.

#[export]
Program Instance Cat_HasTerminal : HasTerminal Cat := {
    term_obj := One;
    term_mor := Fini
}.
Obligation 1.
  destruct f as [F].
  destruct g as [G].
  assert (F = G).
    extensionality e.
    crush.
  replace F with G. subst.
  assert (fmap0 = fmap1).
    extensionality e.
    extensionality f.
    extensionality g.
    crush.
  apply fun_irrelevance.
  assumption.
Qed.

End Hidden.
*)

Class Natural `(F : @Functor C D) `(G : @Functor C D) :=
{ transport  : ∀ {X}, F X ~> G X
; naturality : ∀ {X Y} (f : X ~> Y),
    fmap f ∘ transport = transport ∘ fmap f
}.

Notation "transport/ N" := (@transport _ _ _ _ N _) (at level 24).
Notation "F ⟾ G" := (Natural F G) (at level 90, right associativity).

(* Natural transformations can be applied directly to functorial values to
   perform the functor mapping they imply. *)
Coercion transport : Natural >-> Funclass.

#[export]
Program Instance nat_identity `{F : Functor} : F ⟾ F := {
    transport := fun _ => id
}.
Obligation 1.
  rewrite right_identity.
  rewrite left_identity.
  reflexivity.
Defined.

#[export]
Program Instance nat_compose `{F : C ⟶ D} `{G : C ⟶ D} `{K : C ⟶ D}
  (f : G ⟾ K) (g : F ⟾ G) : F ⟾ K := {
    transport := fun X =>
      @transport C D G K f X ∘ @transport C D F G g X
}.
Obligation 1.
  rewrite comp_assoc.
  rewrite naturality.
  rewrite <- comp_assoc.
  rewrite naturality.
  rewrite comp_assoc.
  reflexivity.
Defined.

Section NaturalEquiv.

Context `{C : Category}.
Context `{D : Category}.
Context `{F : C ⟶ D}.
Context `{G : C ⟶ D}.

Lemma nat_irrelevance : ∀ (f g : ∀ {X}, F X ~> G X) n n',
  @f = @g ->
  {| transport := @f; naturality := n |} =
  {| transport := @g; naturality := n' |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
Qed.

Definition nat_equiv (x y : F ⟾ G) : Prop :=
  match x with
  | Build_Natural _ _ _ _ transport0 _ => match y with
    | Build_Natural _ _ _ _ transport1 _ =>
        forall {X}, transport0 X = transport1 X
    end
  end.

#[export]
Program Instance nat_equivalence : Equivalence nat_equiv.
Obligation 1.
  unfold Reflexive, nat_equiv. intros.
  destruct x. auto.
Defined.
Obligation 2.
  unfold Symmetric, nat_equiv. intros.
  destruct x. destruct y. intros.
  specialize (H X).
  symmetry; assumption.
Defined.
Obligation 3.
  unfold Transitive, nat_equiv. intros.
  destruct x. destruct y. destruct z.
  intros. specialize (H X). specialize (H0 X).
  transitivity (transport1 X); assumption.
Defined.

End NaturalEquiv.

Add Parametric Relation
  `(C : Category) `(D : Category) `(F : C ⟶ D) `(G : C ⟶ D)
  : (F ⟾ G) (@nat_equiv C D F G)
  reflexivity proved by  (@Equivalence_Reflexive  _ _ (@nat_equivalence C D F G))
  symmetry proved by     (@Equivalence_Symmetric  _ _ (@nat_equivalence C D F G))
  transitivity proved by (@Equivalence_Transitive _ _ (@nat_equivalence C D F G))
    as parametric_relation_nat_eqv.

  Add Parametric Morphism
    `(C : Category) `(D : Category) `(F : C ⟶ D) `(G : C ⟶ D) `(K : C ⟶ D)
    : (@nat_compose C D F G K)
    with signature (nat_equiv ==> nat_equiv ==> nat_equiv)
      as parametric_morphism_nat_comp.
    intros. unfold nat_equiv, nat_compose.
    destruct x. destruct y. destruct x0. destruct y0.
    simpl in *. intros.
    specialize (H0 X). rewrite H0. crush.
Defined.

(* Nat is the category whose morphisms are natural transformations between
   Functors from C ⟶ D. *)

#[export]
Program Instance Nat (C : Category) (D : Category) : Category :=
{ ob      := @Functor C D
; hom     := @Natural C D
; id      := @nat_identity C D
; compose := @nat_compose C D
}.
Obligation 1. (* right_identity *)
  destruct f. intros.
  apply nat_irrelevance.
  extensionality x. crush.
Defined.
Obligation 2. (* left_identity *)
  destruct f. intros.
  apply nat_irrelevance.
  extensionality x. crush.
Defined.
Obligation 3. (* comp_assoc *)
  destruct f. destruct g. destruct h.
  apply nat_irrelevance.
  extensionality x. unfold nat_compose.
  simpl. rewrite <- comp_assoc. reflexivity.
Defined.

Notation "[ C , D ]" := (Nat C D) (at level 90, right associativity).

Definition Copresheaves (C : Category) := [C, Sets].
Definition Presheaves   (C : Category) := [C^op, Sets].

(*
Bifunctors can be curried:

  C × D ⟶ E   -->  C ⟶ [D, E]
  ~~~
  (C, D) -> E  -->  C -> D -> E

Where ~~~ should be read as "Morally equivalent to".

Note: We do not need to define Bifunctors as a separate class, since they can
be derived from functors mapping to a category of functors.  So in the
following two definitions, [P] is effectively our bifunctor.

The trick to [bimap] is that both the [Functor] instances we need (for [fmap]
and [fmap1]), and the [Natural] instance, can be found in the category of
functors we're mapping to by applying [P].
*)

Definition fmap1 `{P : C ⟶ [D, E]} {A : C} `(f : X ~{D}~> Y) :
  P A X ~{E}~> P A Y := fmap f.

Definition bimap `{P : C ⟶ [D, E]} {X W : C} {Y Z : D} (f : X ~{C}~> W) (g : Y ~{D}~> Z) :
  P X Y ~{E}~> P W Z := let N := @fmap _ _ P _ _ f in transport/N ∘ fmap1 g.

Definition contramap `{F : C^op ⟶ D} `(f : X ~{C}~> Y) :
  F Y ~{D}~> F X := fmap (unop f).

Definition dimap `{P : C^op ⟶ [D, E]} `(f : X ~{C}~> W) `(g : Y ~{D}~> Z) :
  P W Y ~{E}~> P X Z := bimap (unop f) g.

(* jww (2014-08-24): Waiting on Coq 8.5. *)
(*
#[export]
Program Instance Hom `(C : Category) : C^op ⟶ [C, Sets] :=
{ fobj := fun X =>
  {| fobj := @hom C X
   ; fmap := @compose C X
   |}
; fmap := fun _ _ f => {| transport := fun X g => g ∘ unop f |}
}.
Obligation 1. extensionality x. crush. Defined.
Obligation 2. extensionality x. crush. Defined.
Obligation 3. extensionality x. crush. Defined.
Obligation 4.
  unfold nat_identity.
  apply nat_irrelevance.
  extensionality e.
  extensionality f.
  unfold unop.
  rewrite right_identity.
  auto.
Defined.
Obligation 5.
  unfold nat_compose, nat_identity.
  apply nat_irrelevance.
  extensionality e.
  simpl.
  unfold unop.
  extensionality h.
  crush.
Defined.

Coercion Hom : Category >-> Functor.
*)

(*
(** This is the Yoneda embedding. *)
(* jww (2014-08-10): It should be possible to get rid of Hom here, but the
   coercion isn't firing. *)
#[export]
Program Instance Yoneda `(C : Category) : C ⟶ [C^op, Sets] := Hom (C^op).
Obligation 1. apply op_involutive. Defined.
*)

(*
#[export]
Program Instance YonedaLemma `(C : Category) `(F : C ⟶ Sets) {A : C^op}
    : (C A ⟾ F) ≅Sets F A.
Obligation 1.
  intros.
  destruct X.
  apply transport0.
  simpl.
  destruct C.
  crush.
Defined.
Obligation 2.
  intros.
  simpl.
  pose (@fmap C Sets F A).
  apply Build_Natural with (transport := fun Y φ => h Y φ X).
  intros.
  inversion F. simpl.
  extensionality e.
  unfold h.
  rewrite <- functor_compose_law.
  crush.
Defined.
Obligation 3.
  extensionality e.
  pose (f := fun (_ : unit) => e).
  destruct C.
  destruct F. simpl.
  rewrite functor_id_law0.
  crush.
Qed.
Obligation 4.
  extensionality e.
  destruct e.
  simpl.
  apply nat_irrelevance.
  extensionality f.
  extensionality g.
  destruct C as [ob0 uhom0 hom0 id0].
  destruct F.
  simpl.
  assert (fmap0 A f g (transport0 A (id0 A)) =
          (fmap0 A f g ∘ transport0 A) (id0 A)).
    crush. rewrite H. clear H.
  rewrite naturality0.
  crush.
Qed.
*)

Class FullyFaithful `(F : @Functor C D) :=
{ unfmap : ∀ {X Y : C}, (F X ~> F Y) → (X ~> Y)
}.

(*
#[export]
Program Instance Hom_Faithful (C : Category) : FullyFaithful C :=
{ unfmap := fun _ _ f => (transport/f) id
}.
*)

(*
#[export]
Program Instance Hom_Faithful_Co (C : Category) {A : C} : FullyFaithful (C A).
Obligation 1.
  destruct C. crush.
  clear left_identity.
  clear right_identity.
  clear comp_assoc.
  specialize (compose X A Y).
  apply compose in X0.
    assumption.
  (* jww (2014-08-12): Is this even provable?  Ed thinks no. *)
*)

(** ** Opposite functor[edit]

Every functor [F: C ⟶ D] induces the opposite functor [F^op]: [C^op ⟶ D^op],
where [C^op] and [D^op] are the opposite categories to [C] and [D].  By
definition, [F^op] maps objects and morphisms identically to [F].

*)

#[export]
Program Instance Opposite_Functor `(F : C ⟶ D) : C^op ⟶ D^op := {
    fobj := @fobj C D F;
    fmap := fun X Y f => @fmap C D F Y X (op f)
}.
Obligation 1. unfold op. apply functor_id_law. Defined.
Obligation 2. unfold op. apply functor_compose_law. Defined.

(* jww (2014-08-10): Until I figure out how to make C^op^op implicitly unify
   with C, I need a way of undoing the action of Opposite_Functor. *)
(*
#[export]
Program Instance Reverse_Opposite_Functor `(F : C^op ⟶ D^op) : C ⟶ D := {
    fobj := @fobj _ _ F;
    fmap := fun X Y f => unop (@fmap _ _ F Y X f)
}.
Obligation 1.
  unfold unop.
  unfold fmap. simpl.
  pose (@functor_id_law _ _ F).
  unfold fmap in e. simpl in e.
  specialize (e X). auto.
Qed.
Obligation 2.
  unfold unop.
  unfold fmap. simpl.
  pose (@functor_compose_law _ _ F).
  unfold fmap in e. simpl in e.
  specialize (e Z Y X g f).
  auto.
Qed.
*)

(* Definition Coerce_Functor `(F : C ⟶ D) := Opposite_Functor F. *)

(* Coercion Coerce_Functor : Functor >-> Functor. *)

(*
Lemma op_functor_involutive `(F : Functor)
  : Reverse_Opposite_Functor (Opposite_Functor F) = F.
Proof.
  unfold Reverse_Opposite_Functor.
  unfold Opposite_Functor.
  destruct F.
  apply fun_irrelevance.
  auto.
Qed.
*)

(*
Class Adjunction `{C : Category} `{D : Category}
    `(F : @Functor D C) `(U : @Functor C D) := {
    adj : ∀ (a : D) (b : C), (C (F a) b) ≅ (D a (U b))
}.

Notation "F ⊣ G" := (Adjunction F G) (at level 70) : category_scope.

#[export]
Program Instance adj_identity `{C : Category} : Id ⊣ Id.

(* Definition adj' `{C : Category} `{D : Category} `{E : Category} *)
(*    (F : Functor D C) (U : Functor C D) *)
(*    (F' : Functor E D) (U' : Functor D E)  (a : E) (b : C) *)
(*    : (C (fun_compose F F' a) b) ≅ (E a (fun_compose U' U b)). *)

Definition adj_compose `{C : Category} `{D : Category} `{E : Category}
   (F : Functor D C) (U : Functor C D)
   (F' : Functor E D) (U' : Functor D E)
   (X : F ⊣ U) (Y : F' ⊣ U')
   : @fun_compose E D C F F' ⊣ @fun_compose C D E U' U.
Proof.
  destruct X.
  destruct Y.
  apply (@Build_Adjunction C E (@fun_compose E D C F F') (@fun_compose C D E U' U)).
  intros.
  specialize (adj0 (F' a) b).
  specialize (adj1 a (U b)).
  replace ((E a) ((fun_compose U' U) b)) with ((E a) ((U' (U b)))).
  replace ((C ((fun_compose F F') a)) b) with ((C (F (F' a))) b).
  apply (@iso_compose Sets ((C (F (F' a))) b) ((D (F' a)) (U b)) ((E a) (U' (U b)))).
  assumption.
  assumption.
  crush.
  crush.
Qed.

Record Adj_Morphism `{C : Category} `{D : Category} := {
    free_functor : Functor D C;
    forgetful_functor : Functor C D;
    adjunction : free_functor ⊣ forgetful_functor
}.

(* Lemma adj_left_identity `(F : @Functor D C) `(U : @Functor C D) *)
(*   : adj_compose Id Id F U adj_identity (F ⊣ U) = F ⊣ U. *)
(* Proof. *)
(*   destruct F. *)
(*   unfold fun_compose. *)
(*   simpl. *)
(*   apply fun_irrelevance. *)
(*   extensionality e. *)
(*   extensionality f. *)
(*   extensionality g. *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma adj_right_identity `(F : @Functor C D) : fun_compose F Id = F. *)
(* Proof. *)
(*   destruct F. *)
(*   unfold fun_compose. *)
(*   simpl. *)
(*   apply fun_irrelevance. *)
(*   extensionality e. *)
(*   extensionality f. *)
(*   extensionality g. *)
(*   reflexivity. *)
(* Qed. *)

Lemma adj_irrelevance
   `{C : Category} `{D : Category} `{E : Category}
   (F F' : Functor D C) (U U' : Functor C D)
  : ∀ (X : F ⊣ U) (X' : F' ⊣ U'),
  @F = @F' →
  @U = @U' →
  {| free_functor      := @F
   ; forgetful_functor := @U
   ; adjunction        := @X
   |} =
  {| free_functor      := @F'
   ; forgetful_functor := @U'
   ; adjunction        := @X'
   |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
Qed.

#[export]
Program Instance Adj : Category := {
    ob := Category;
    hom := @Adj_Morphism
}.
Obligation 1.
  apply Build_Adj_Morphism
    with (free_functor      := Id)
         (forgetful_functor := Id).
  apply adj_identity.
Defined.
Obligation 2.
  destruct X.
  destruct X0.
  apply Build_Adj_Morphism
    with (free_functor      := fun_compose free_functor1 free_functor0)
         (forgetful_functor := fun_compose forgetful_functor0 forgetful_functor1).
  apply adj_compose.
  assumption.
  assumption.
Defined.
Obligation 3.
  unfold Adj_obligation_2.
  unfold Adj_obligation_1.
  destruct f.
  destruct adjunction0.
  simpl.
  pose (fun_left_identity free_functor0).
  pose (fun_right_identity forgetful_functor0).
  apply adj_irrelevance.
  rewrite e. reflexivity.
  rewrite e0. reflexivity.
Qed.
Obligation 4.
  unfold Adj_obligation_2.
  unfold Adj_obligation_1.
  destruct f.
  destruct adjunction0.
  simpl.
  pose (fun_left_identity forgetful_functor0).
  pose (fun_right_identity free_functor0).
  apply adj_irrelevance.
  rewrite e0. reflexivity.
  rewrite e. reflexivity.
Qed.
Obligation 5.
  admit.
Qed.
*)

(* Inductive Const := Const_ : Type → Const. *)

(* Definition getConst `{C : Category} (c : @Const C) : C := *)
(*   match c with *)
(*   | Const_ x => x *)
(*   end. *)

#[export]
Program Instance Const `{C : Category} `{J : Category} (x : C) : J ⟶ C := {
    fobj := fun _ => x;
    fmap := fun _ _ _ => id
}.

Lemma Const_Iso `{C : Category} : ∀ a b, Const a b ≅ a.
Proof. crush. Qed.

Definition Sets_getConst `{J : Category} (a : Type) (b : J)
  (c : @Const Sets J a b) : Type := @fobj J Sets (@Const Sets J a) b.

#[export]
Program Instance Const_Transport `(C : Category) `(J : Category) `(x ~> y)
  : @Natural C J (Const x) (Const y) := {
    transport := fun X => _
}.
Obligation 2.
  rewrite left_identity.
  rewrite right_identity. reflexivity.
Defined.

#[export] Hint Unfold Const_Transport : core.

#[export]
Program Instance Delta `{C : Category} `{J : Category} : C ⟶ [J, C] := {
    fobj := @Const C J;
    fmap := @Const_Transport J C
}.
Obligation 1.
  autounfold.
  unfold nat_compose.
  apply nat_irrelevance.
  extensionality x0. crush.
Qed.
Obligation 2.
  autounfold.
  unfold nat_compose.
  apply nat_irrelevance.
  extensionality x0. crush.
Qed.

(*
Class Complete `(C : Category) := {
    complete : ∀ (J : Category), { Lim : [J, C] ⟶ C & @Delta C J ⊣ Lim }
}.
*)

(* Here F is a diagram of type J in C. *)
Record Cone `{C : Category} `{J : Category} (n : C) `(F : @Functor J C) := {
    cone_mor : ∀ j : J, n ~> F j;
    cone_law : ∀ i j (f : i ~{J}~> j), (@fmap J C F i j f) ∘ cone_mor i = cone_mor j
}.

Definition Const_to_Cone `(F : J ⟶ C) {a} : (Const a ⟾ F) → Cone a F.
Proof.
  intros.
  destruct X.
  apply Build_Cone
    with (cone_mor := transport0).
  intros. simpl in *.
  specialize (naturality0 i j f).
  rewrite right_identity in naturality0.
  apply naturality0.
Defined.

Definition Cone_to_Const `(F : J ⟶ C) {a} : Cone a F → (Const a ⟾ F).
Proof.
  unfold Const. intros.
  destruct X. destruct F.
  refine (Build_Natural _ _ _ _ _ _); intros; simpl.
  crush. rewrite right_identity.
  apply cone_law0.
Defined.

(* jww (2014-08-24): Need Coq 8.5
#[export]
Program Instance Const_Cone_Iso `(F : J ⟶ C)
  : ∀ a, (Const a ⟾ F) ≅Sets Cone a F := {
    to   := @Const_to_Cone J C F a;
    from := @Cone_to_Const J C F a
}.
Obligation 1.
  extensionality x.
  destruct x. destruct F.
  simpl in *. f_equal.
  extensionality i.
  extensionality j.
  extensionality f.
  destruct C.
  destruct J. simpl. crush.
Qed.
Obligation 2.
Abort.
*)

(*
#[export]
Program Instance Lim_Sets `(J : Category) : [J, Sets] ⟶ Sets := {
    fobj := fun F => 
    fmap := fun _ _ n F_x z => (transport/n) (F_x z)
}.

Lemma distribute_forall : ∀ a {X} P, (a → ∀ (x : X), P x) → (∀ x, a → P x).
Proof.
  intros.
  apply X0.
  assumption.
Qed.

Lemma forall_distribute : ∀ a {X} P, (∀ x, a → P x) → (a → ∀ (x : X), P x).
Proof.
  intros.
  apply X0.
  assumption.
Qed.

#[export]
Program Instance Sets_Const_Nat (J : Category) (F : [J, Sets])
  (a : Type) (f : a → ∀ x : J, F x) : @Const Sets J a ⟾ F.
Obligation 2.
  extensionality e.
  unfold Sets_Const_Nat_obligation_1.
  remember (f e) as j.
  destruct F. simpl. clear.
  destruct J.
  crush. clear.
  (* jww (2014-08-12): We don't believe this is true. *)

#[export]
Program Instance Sets_Const_Lim_Iso (J : Category) (a : Sets) (F : [J, Sets])
  : @Isomorphism Sets (Const a ⟾ F) (a → Lim_Sets J F).
Obligation 1.
  destruct F. simpl.
  destruct X.
  apply transport0.
  auto.
Defined.
Obligation 2.
  apply Sets_Const_Nat.
  auto.
Defined.
Obligation 3.
  extensionality e.
  unfold Sets_Const_Lim_Iso_obligation_1.
  unfold Sets_Const_Lim_Iso_obligation_2.
  extensionality f.
  extensionality g.
  destruct F. simpl.
  unfold Sets_Const_Nat_obligation_1.
  reflexivity.
Qed.
Obligation 4.
  extensionality e.
  unfold Sets_Const_Lim_Iso_obligation_1.
  unfold Sets_Const_Lim_Iso_obligation_2.
  unfold Sets_Const_Nat.
  destruct e.
  unfold Sets_Const_Nat_obligation_1.
  unfold Sets_Const_Nat_obligation_2.
  apply nat_irrelevance.
  extensionality f.
  extensionality g.
  destruct F. simpl.
  reflexivity.
Qed.

#[export]
Program Instance Sets_Complete : Complete Sets.
Obligation 1.
  exists (Lim_Sets J).
  apply Build_Adjunction.
  intros. simpl.
  apply Sets_Const_Lim_Iso.
Qed.
*)

Definition EndoFunctor `(C : Category) := C ⟶ C.

Definition CoqEndoFunctor := Sets ⟶ Sets.

Reserved Notation "X ⊗ Y" (at level 27, right associativity).

Class MonoidalCategory := {
    is_category :> Category;

    mult  : is_category ⟶ [is_category, is_category] where "X ⊗ Y" := (mult X Y);
    nelem : is_category;

    mc_left_id  : ∀ X, X ⊗ nelem ≅ X;
    mc_right_id : ∀ X, nelem ⊗ X ≅ X;
    mc_assoc    : ∀ X Y Z, (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)
}.

Infix "⊗" := mult (at level 27, right associativity) : category_scope.

Coercion is_category : MonoidalCategory >-> Category.

#[export]
Program Instance Tuple_Functor (X : Type) : Sets ⟶ Sets := {
    fobj := fun Y => (X * Y);
    fmap := fun _ _ f p => match p with
      (x, y) => (x, f y)
    end
}.
Obligation 1.
  extensionality p.
  destruct p. reflexivity.
Qed.
Obligation 2.
  extensionality p.
  destruct p. reflexivity.
Qed.

#[export]
Program Instance Tuple_Bifunctor : Sets ⟶ [Sets, Sets] := {
    fobj := Tuple_Functor;
    fmap := fun _ _ f =>
      {| transport := fun _ p =>
           match p with (x, y) => (f x, y) end
       |}
}.
Obligation 1.
  extensionality p.
  destruct p. reflexivity.
Qed.
Obligation 2.
  unfold nat_identity.
  apply nat_irrelevance.
  extensionality H.
  extensionality p.
  destruct p. reflexivity.
Qed.
Obligation 3.
  unfold nat_compose.
  apply nat_irrelevance.
  extensionality H.
  extensionality p.
  destruct p. reflexivity.
Qed.

#[export]
Program Instance LTuple_Isomorphism {A} : (unit * A) ≅Sets A :=
{ to   := @snd unit A
; from := pair tt
}.
Obligation 2.
  extensionality x. destruct x. destruct u. reflexivity.
Qed.

#[export]
Program Instance RTuple_Isomorphism {A} : (A * unit) ≅Sets A :=
{ to   := @fst A unit
; from := fun x => (x, tt)
}.
Obligation 2.
  extensionality x. destruct x. destruct u. reflexivity.
Qed.

Definition tuple_swap_a_bc_to_ab_c {A B C} (x : A * (B * C)) : A * B * C :=
  match x with (a, (b, c)) => ((a, b), c) end.

Definition tuple_swap_ab_c_to_a_bc {A B C} (x : A * B * C) : A * (B * C) :=
  match x with ((a, b), c) => (a, (b, c)) end.

Definition left_triple {A B C} (x : A) (y : B) (z : C) : A * B * C :=
  ((x, y), z).

Definition right_triple {A B C} (x : A) (y : B) (z : C) : A * (B * C) :=
  (x, (y, z)).

#[export]
Program Instance Tuple_Assoc {A B C} : (A * B * C) ≅Sets (A * (B * C)) :=
{ to   := tuple_swap_ab_c_to_a_bc
; from := tuple_swap_a_bc_to_ab_c
}.
Next Obligation. (* iso_to *)
  intros.
  extensionality x.
  unfold compose.
  destruct x.
  destruct p.
  unfold id.
  unfold tuple_swap_a_bc_to_ab_c, tuple_swap_ab_c_to_a_bc.
  reflexivity.
Defined.
Next Obligation. (* iso_from *)
  intros.
  extensionality x.
  unfold compose.
  destruct x.
  destruct p.
  unfold id.
  unfold tuple_swap_a_bc_to_ab_c, tuple_swap_ab_c_to_a_bc.
  reflexivity.
Defined.

Definition uncurry {X Y Z} (f : X -> Y -> Z) (xy : X * Y) : Z :=
  match xy with (x, y) => f x y end.

Theorem uncurry_works : forall {X Y Z} (x : X) (y : Y) (f : X -> Y -> Z),
  uncurry f (x, y) = f x y.
Proof. reflexivity. Qed.

#[export]
Program Instance Sets_with_Products : MonoidalCategory := {
    is_category := Sets;

    mult  := Tuple_Bifunctor;
    nelem := unit;

    mc_left_id  := @RTuple_Isomorphism;
    mc_right_id := @LTuple_Isomorphism;
    mc_assoc    := @Tuple_Assoc
}.

Reserved Notation "f ** g" (at level 28, left associativity).

Class LaxMonoidalFunctor `(C : MonoidalCategory) `(D : MonoidalCategory) := {
    lmf_functor :> C ⟶ D;

    lmf_id  : nelem ~> fobj nelem;
    ap_prod : ∀ X Y, fobj X ⊗ fobj Y ~> fobj (X ⊗ Y)
      where "f ** g" := (ap_prod f g);

    lmf_left_id  : ∀ X, fobj X ⊗ nelem ≅ fobj (X ⊗ nelem);
    lmf_right_id : ∀ X, nelem ⊗ fobj X ≅ fobj (nelem ⊗ X);
    lmf_assoc    : ∀ X Y Z, (fobj X ⊗ fobj Y) ⊗ fobj Z ≅ fobj (X ⊗ (Y ⊗ Z))
}.
