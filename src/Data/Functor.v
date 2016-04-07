Require Import Hask.Ltac.
Require Import Hask.Control.Category.

Generalizable All Variables.

Section Functor.

Context `{Category C}.
Context `{Category D}.

Class Functor : Type := {
  fobj : C -> D;
  fmap : forall {a b : C}, (a ~> b) -> (fobj a ~> fobj b);
  fmap_proper :> forall {a b : C} , Proper (equiv ==> equiv) (@fmap a b)
}.

End Functor.

Arguments fobj {_ _ _ _ _ _ _} _.
Arguments fmap {_ _ _ _ _ _ _ a b} _.

Coercion fobj : Functor >-> Funclass.

Infix "<$>" := fmap (at level 28, left associativity, only parsing).
Infix "<$[ M ]>" :=
  (@fmap _ _ _ _ _ _ M _ _) (at level 28, left associativity, only parsing).
Notation "x <&> f" :=
  (fmap f x) (at level 28, left associativity, only parsing).

Notation "fobj[ M ]" := (@fobj _ _ _ _ _ _ M) (at level 9).
Notation "fmap[ M ]" := (@fmap _ _ _ _ _ _ M _ _) (at level 9).
Notation "fmap[ M N ]" :=
  (@fmap _ _ _ _ _ _ (fun X => M (N X)) _ _) (at level 9).
Notation "fmap[ M N O ]" :=
  (@fmap _ _ _ _ _ _ (fun X => M (N (O X))) _ _) (at level 9).

Notation "C ⟶ D" :=
  (@Functor C _ _ D _ _) (at level 90, right associativity).

Program Instance Compose_Functor `{Category C} `{Category D} `{Category E}
  `{F : D ⟶ E} `{G : C ⟶ D} : C ⟶ E :=
{ fobj := F \o G;
  fmap := fun _ _ => fmap[F] \o fmap[G]
}.
Obligation 1.
  intros f f' Hf.
  unfold Ltac.comp.
  rewrite Hf.
  reflexivity.
Defined.

(* Mapping from any Coq Type to a Coq function (Type -> Type). This means that
   fmap maps Coq function to functions between functions, and we can't prove
   that fmap respects hom-set equivalences unless we know about equivalences
   between such functions. *)
Program Instance Impl_FunctorDirect (A : Type) : Coq ⟶ Coq := {
  fobj := fun B : Type => A -> B;
  fmap := fun X Y (f : X -> Y) (x : A -> X) (a : A) => f (x a)
}.
Next Obligation.
  intros ?? H x.
  Require Import FunctionalExtensionality.
  extensionality a0.
  rewrite H.
  reflexivity.
Qed.

Program Instance Extensional_Equivalence {A B : Type} :
  Equivalence (fun f g : A -> B => forall x : A, f x = g x).
Next Obligation.
  intros x y z H1 H2 a.
  transitivity (y a); [ apply H1 | apply H2 ].
Defined.

(* The problem with Impl_FunctorDirect can be solved if we instead map Coq
   types to a category whose objects (Coq functions, in this case) are setoids
   (just as our hom-sets were), so now we can easily state that the hom-set
   equivalences will be mapped to the object (function) equivalences. *)
Program Instance Impl_Functor (A : Type) : Coq ⟶ SetoidCoq := {
  fobj := fun B : Type =>
            {| carrier   := A -> B
             ; is_setoid := {| equiv := fun f g => forall x, f x = g x
                             ; setoid_equiv := Extensional_Equivalence |} |};
  fmap := fun X Y (f : X -> Y) =>
            {| morph := fun x a => f (x a)
             ; proper_morph := _ |}
}.
Next Obligation.
  intros ?? H ?; rewrite H; reflexivity.
Defined.
Next Obligation.
  intros ?? H ??; simpl; rewrite H; reflexivity.
Defined.

(* Or we can go whole hog and just say that some setoid is mapped to a
   category of setoids of functions. This gets very verbose, however. *)
Program Instance Impl_SetoidFunctor (A : Objects) : SetoidCoq ⟶ SetoidCoq := {
  fobj := fun B : Objects =>
            {| carrier   := @SetoidMorphism A is_setoid B is_setoid
             ; is_setoid := @Arr_Setoid A B |};
  fmap := fun X Y (f : X ~> Y) =>
            {| morph := fun x =>
                 {| morph := morph f \o morph x
                  ; proper_morph := _ |}
             ; proper_morph := _ |}
}.
Next Obligation.
  intros ?? H.
  unfold Ltac.comp.
  apply proper_morph.
  apply proper_morph.
  exact H.
Defined.
Next Obligation.
  intros ?? H.
  simpl; intros.
  apply proper_morph.
  apply H.
Defined.
Next Obligation.
  intros ?? H.
  simpl; intros.
  apply H.
Defined.

Module FunctorLaws.

Require Import FunctionalExtensionality.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

Section FunctorLaws.

Context `{Category C}.
Context `{Category D}.

Class FunctorLaws `{F : C ⟶ D} := {
  fmap_id   : forall a : C, fmap[F] id/a == id;
  fmap_comp : forall (a b c : C) (f : b ~> c) (g : a ~> b),
    fmap f ∘ fmap g == fmap[F] (f ∘ g)
}.

(*
Corollary fmap_id_x `{FunctorLaws f} : forall (a : Type) x, fmap (@id a) x = x.
Proof.
  intros.
  rewrite fmap_id.
  reflexivity.
Qed.

Corollary fmap_comp_x `{FunctorLaws F} :
  forall (a b c : Type) (f : b -> c) (g : a -> b) x,
  fmap f (fmap g x) = fmap (fun y => f (g y)) x.
Proof.
  intros.
  replace (fun y : a => f (g y)) with (f \o g).
    rewrite <- fmap_comp.
    reflexivity.
  reflexivity.
Qed.
*)

(*
Corollary fmap_compose  `{Functor F} `{Functor G} : forall {X Y} (f : X -> Y),
  @fmap F _ (G X) (G Y) (@fmap G _ X Y f) = @fmap (F \o G) _ X Y f.
Proof. reflexivity. Qed.
*)

End FunctorLaws.

Program Instance Compose_FunctorLaws
  `{Category C} `{Category D} `{Category E}
  `{@FunctorLaws D _ _ E _ _ F} `{@FunctorLaws C _ _ D _ _ G} :
  @FunctorLaws C _ _ E _ _ (@Compose_Functor _ _ _ _ _ _ _ _ _ F G).
Obligation 1. do 2 rewrite fmap_id;   reflexivity. Qed.
Obligation 2. do 2 rewrite fmap_comp; reflexivity. Qed.

Program Instance Impl_FunctorLaws {A : Type} :
  @FunctorLaws Coq _ _ SetoidCoq _ _ (Impl_Functor A).

End FunctorLaws.

Section Natural.

Context `{Category C}.
Context `{Category D}.

Class Natural `{F : C ⟶ D} `{G : C ⟶ D} :=
{ transport  : forall {X}, fobj[F] X ~> fobj[G] X
; naturality : forall {X Y} (f : X ~> Y),
    fmap[G] f ∘ transport == transport ∘ fmap[F] f
}.

Notation "transport/ N" := (@transport _ _ N) (at level 44).
Notation "F ⟾ G" := (@Natural F G) (at level 90, right associativity).

(* Natural transformations can be applied directly to functorial values to
   perform the functor mapping they imply. *)
Coercion transport : Natural >-> Funclass.

Instance Functor_Arrows : @Arrows (C ⟶ D) := {
  Hom := fun (f g : C ⟶ D) => f ⟾ g
}.

Program Instance Natural_Setoid `{F : C ⟶ D} `{G : C ⟶ D} : Setoid (F ⟾ G) := {
  equiv := fun (f g : F ⟾ G) => forall x, f x == g x
}.
Obligation 1.
  constructor; repeat intro.
  - reflexivity.
  - symmetry. apply H1.
  - transitivity (y x0). apply H1. apply H2.
Qed.

Program Instance Nat : @Category (C ⟶ D) Functor_Arrows := {
  id   := fun A => {| transport := fun _ => id |};
  comp := fun F G H A1 A2 =>
            {| transport := fun x =>
                 @transport G H A1 x ∘ @transport F G A2 x |}
}.
Next Obligation.
  rewrite right_id, left_id;
  reflexivity.
Defined.
Next Obligation.
  rewrite comp_assoc, naturality, <- comp_assoc, naturality, comp_assoc;
  reflexivity.
Defined.
Next Obligation.
  intros ?? H1 ?? H2 x; simpl.
  rewrite H1, H2; reflexivity.
Defined.
Next Obligation.
  apply comp_assoc.
Qed.

End Natural.

Notation "transport/ N" := (@transport _ _ _ _ _ _ _ _ N) (at level 44).
Notation "F ⟾ G" :=
  (@Natural _ _ _ _ _ _ F G) (at level 90, right associativity).

Notation "[ C , D ]" := (Nat C _ _ D _ _) (at level 90, right associativity).

Program Instance Id_Functor `{Category C} : C ⟶ C := {
  fobj := fun A => A;
  fmap := _
}.
