Require Import Hask.Ltac.
Require Import Hask.Control.Category.

Generalizable All Variables.

Section Functor.

Context `{Category C}.
Context `{Category D}.

Class Functor : Type := {
  fobj : C -> D;
  fmap : forall {a b : C}, (a ~> b) -> fobj a ~> fobj b;
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

Program Instance Impl_Functor (A : Objects) : Coq ⟶ Coq := {
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

(* Functors preserve extensional equality for the applied function.
   This is needed to perform setoid rewriting within the function
   passed to a functor. *)
Add Parametric Morphism {A B} `{Functor F} : (@fmap F _ A B)
  with signature (pointwise_relation _ eq ==> eq ==> eq)
    as mul_isomorphism.
Proof.
  intros.
  f_equal.
  extensionality e.
  apply H0.
Qed.

Class FunctorLaws (f : Type -> Type) `{Functor f} := {
  fmap_id   : forall a : Type, fmap (@id a) = id;
  fmap_comp : forall (a b c : Type) (f : b -> c) (g : a -> b),
    fmap f \o fmap g = fmap (f \o g)
}.

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

Corollary fmap_compose  `{Functor F} `{Functor G} : forall {X Y} (f : X -> Y),
  @fmap F _ (G X) (G Y) (@fmap G _ X Y f) = @fmap (F \o G) _ X Y f.
Proof. reflexivity. Qed.

Program Instance Compose_FunctorLaws `{FunctorLaws F} `{FunctorLaws G} :
  FunctorLaws (F \o G).
Obligation 1. (* fmap_id *)
  extensionality x.
  do 2 rewrite fmap_id.
  reflexivity.
Qed.
Obligation 2. (* fmap_comp *)
  extensionality x.
  do 2 rewrite fmap_comp.
  reflexivity.
Qed.

Program Instance Impl_FunctorLaws {A} : FunctorLaws (fun B => A -> B).

End FunctorLaws.
