Require Import Hask.Prelude.
Require Import Hask.Ltac.
Require Import Hask.Control.Monad.
Require Import Hask.Control.Iso.

Generalizable All Variables.

Definition Yoneda (f : Type -> Type) (a : Type) :=
  forall r : Type, (a -> r) -> f r.

Instance Yoneda_lemma `{Functor f} : forall a, Yoneda f a ≅ f a := {
  iso_to   := fun x => x _ id;
  iso_from := fun x _ k => fmap k x
}.

Instance Yoneda_Functor {f : Type -> Type} : Functor (Yoneda f) := {
  fmap := fun _ _ g k _ h => k _ (h \o g)
}.

Instance Yoneda_Applicative `{Applicative f} :
  Applicative (Yoneda f) := {
  pure := fun _ x => fun _ k => pure (k x);
  ap   := fun a b g x => fun _ k => g _ (comp k) <*> iso_to x
}.

Definition Yoneda_join `{Monad m} `(k : Yoneda m (Yoneda m a)) : Yoneda m a :=
  fun _ h => join (k _ (fun y => y _ h)).

Instance Yoneda_Monad `{Monad m} : Monad (Yoneda m) := {
  join := @Yoneda_join m _
}.

Module YonedaLaws.

Require Import FunctionalExtensionality.

Include IsomorphismLaws.
Include MonadLaws.

(* Parametricity theorem. *)
Axiom fmap_cps : forall `{Functor f} a b c (k : forall r, (a -> r) -> f r)
  (g : b -> c) (h : a -> b), fmap g (k _ h) = k _ (g \o h).

Program Instance Yoneda_lemma `{FunctorLaws f} :
  forall a, @IsomorphismLaws (Yoneda f a) (f a) (Yoneda_lemma a).
Obligation 1.
  extensionality x.
  simpl.
  extensionality r.
  extensionality g.
  apply fmap_cps.
Qed.
Obligation 2.
  extensionality x.
  unfold comp.
  rewrite fmap_id.
  reflexivity.
Qed.

Program Instance Yoneda_FunctorLaws {f : Type -> Type} : FunctorLaws (Yoneda f).

Program Instance Yoneda_ApplicativeLaws `{ApplicativeLaws f} :
  ApplicativeLaws (Yoneda f).
Obligation 1.
  extensionality x.
  extensionality r.
  extensionality k0.
  rewrite ap_fmap, <- fmap_comp, fmap_id.
  unfold comp, id.
  apply fmap_cps.
Qed.
Obligation 2.
  extensionality r.
  extensionality k.
  rewrite <- ap_comp; f_equal.
  repeat rewrite ap_fmap; f_equal.
  repeat rewrite fmap_cps; f_equal.
Qed.
Obligation 3.
  extensionality r.
  extensionality k.
  rewrite ap_fmap.
  unfold comp.
  rewrite <- fmap_comp_x.
  repeat rewrite fmap_pure_x.
  reflexivity.
Qed.
Obligation 4.
  extensionality r.
  extensionality k.
  rewrite ap_fmap, <- fmap_comp, ap_interchange.
  unfold comp.
  rewrite ap_fmap.
  repeat rewrite fmap_cps.
  f_equal.
Qed.
Obligation 5.
  extensionality k.
  extensionality r.
  extensionality g.
  rewrite ap_fmap, <- fmap_comp_x.
  unfold comp.
  repeat rewrite fmap_cps.
  f_equal.
Qed.

Program Instance Yoneda_MonadLaws `{MonadLaws m} : MonadLaws (Yoneda m).
Obligation 1.
  extensionality k.
  unfold Yoneda_join.
  extensionality r.
  extensionality h.
  simpl.
  rewrite <- join_fmap_join_x, fmap_cps.
  reflexivity.
Qed.
Obligation 2.
  extensionality k.
  unfold Yoneda_join.
  extensionality r.
  extensionality h.
  unfold comp.
  replace (fun x : a => pure[m] (h x)) with (pure[m] \o h).
    rewrite <- fmap_cps.
    rewrite join_fmap_pure_x.
    reflexivity.
  reflexivity.
Qed.
Obligation 3.
  extensionality k.
  unfold Yoneda_join.
  extensionality r.
  extensionality h.
  unfold comp.
  rewrite join_pure_x.
  reflexivity.
Qed.

End YonedaLaws.

(**************************************************************************)

(* The contravariant Yoneda lemma, made applicable to covariant functors by
   changing it from a universally quantified function to an existentially
   quantified construction of two arguments. *)

Inductive Coyoneda (f : Type -> Type) (a : Type) :=
  COYO : forall x, (x -> a) -> f x -> Coyoneda f a.

Arguments COYO {f a x} _ _.

Definition liftCoyoneda {f : Type -> Type} {a : Type} : f a -> Coyoneda f a :=
  COYO id.

Definition lowerCoyoneda `{Functor f} {a : Type} (c : Coyoneda f a) : f a :=
  match c with COYO _ g h => fmap g h end.

Instance Coyoneda_Functor (f : Type -> Type) : Functor (Coyoneda f) := {
  fmap := fun _ _ f x => match x with COYO _ g h => COYO (f \o g) h end
}.

Module CoyonedaLaws.

Include FunctorLaws.

Require Import FunctionalExtensionality.

Program Instance Coyoneda_FunctorLaws (f : Type -> Type) :
  FunctorLaws (Coyoneda f).
Obligation 1. extensionality x. destruct x; reflexivity. Qed.
Obligation 2. extensionality x. destruct x; reflexivity. Qed.

Theorem coyo_to `{FunctorLaws f} : forall a (x : f a),
  lowerCoyoneda (liftCoyoneda x) = x.
Proof.
  intros a x.
  unfold lowerCoyoneda, liftCoyoneda.
  rewrite fmap_id.
  reflexivity.
Qed.

Theorem coyo_lower_naturality `{FunctorLaws f} : forall a b (g : a -> b),
  fmap g \o lowerCoyoneda (f:=f) = lowerCoyoneda \o fmap g.
Proof.
  intros a b k.
  extensionality x.
  destruct x as [x g h]; simpl.
  rewrite fmap_comp_x.
  reflexivity.
Qed.

Axiom coyo_parametricity : forall `{FunctorLaws f} a b (g : a -> b),
  COYO g = COYO id \o fmap g.

Theorem coyo_lift_naturality `{FunctorLaws f} : forall a b (g : a -> b),
  fmap g \o liftCoyoneda (f:=f) = liftCoyoneda \o fmap g.
Proof.
  intros a b g.
  unfold liftCoyoneda.
  extensionality x.
  simpl.
  replace (g \o id) with g; auto.
  rewrite coyo_parametricity.
  reflexivity.
Qed.

Theorem coyo_from `{FunctorLaws f} : forall a (x : Coyoneda f a),
  liftCoyoneda (lowerCoyoneda x) = x.
Proof.
  intros a [x g h].
  unfold lowerCoyoneda.
  replace (liftCoyoneda ((fmap[f] g) h)) with ((liftCoyoneda \o (fmap[f] g)) h).
    rewrite <- coyo_lift_naturality.
    reflexivity.
  reflexivity.
Qed.

End CoyonedaLaws.
