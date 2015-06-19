Require Import Hask.Prelude.
Require Import Hask.Control.Monad.
Require Import Hask.Control.Iso.

Generalizable All Variables.

Definition Yoneda (f : Type -> Type) (a : Type) :=
  forall r : Type, (a -> r) -> f r.

Program Instance Yoneda_lemma `{Functor f} : forall a, Yoneda f a ≅ f a := {
  iso_to   := fun x => x _ id;
  iso_from := fun x => fun _ k => fmap k x
}.

Program Instance Yoneda_Functor {f : Type -> Type} : Functor (Yoneda f) := {
  fmap := fun _ _ g k => fun _ h => k _ (h \o g)
}.

Program Instance Yoneda_Applicative `{Applicative f} :
  Applicative (Yoneda f) := {
  pure := fun _ x => fun _ k => pure (k x);
  ap   := fun a b g x => fun _ k => g _ (comp k) <*> iso_to x
}.

Definition Yoneda_join `{Monad m} `(k : Yoneda m (Yoneda m a)) : Yoneda m a :=
  fun _ h => join (k _ (fun y => y _ h)).

Program Instance Yoneda_Monad `{Monad m} : Monad (Yoneda m) := {
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
  move=> x /=.
  extensionality r.
  extensionality g.
  exact: fmap_cps.
Qed.
Obligation 2.
  move=> x.
  by rewrite /funcomp fmap_id.
Qed.

Program Instance Yoneda_FunctorLaws {f : Type -> Type} : FunctorLaws (Yoneda f).

Program Instance Yoneda_ApplicativeLaws `{ApplicativeLaws f} :
  ApplicativeLaws (Yoneda f).
Obligation 1.
  move=> x /=.
  extensionality r.
  extensionality k0.
  rewrite ap_fmap -fmap_comp /funcomp fmap_id.
  exact: fmap_cps.
Qed.
Obligation 2.
  extensionality r.
  extensionality k.
  rewrite -ap_comp; f_equal.
  rewrite !ap_fmap; f_equal.
  rewrite !fmap_cps; f_equal.
Qed.
Obligation 3.
  extensionality r.
  extensionality k.
  by rewrite ap_fmap /compose -fmap_comp /funcomp !fmap_pure_x.
Qed.
Obligation 4.
  extensionality r.
  extensionality k.
  rewrite ap_fmap -fmap_comp ap_interchange /funcomp
          ap_fmap !fmap_cps.
  f_equal.
Qed.
Obligation 5.
  move=> k /=.
  extensionality r.
  extensionality g.
  rewrite ap_fmap -fmap_comp /funcomp !fmap_cps.
  f_equal.
Qed.

Program Instance Yoneda_MonadLaws `{MonadLaws m} : MonadLaws (Yoneda m).
Obligation 1.
  move=> k /=.
  rewrite /Yoneda_join.
  extensionality r.
  extensionality h.
  by rewrite -join_fmap_join_x fmap_cps.
Qed.
Obligation 2.
  move=> k /=.
  rewrite /Yoneda_join.
  extensionality r.
  extensionality h.
  by rewrite -fmap_cps join_fmap_pure_x.
Qed.
Obligation 3.
  move=> k /=.
  rewrite /Yoneda_join.
  extensionality r.
  extensionality h.
  by rewrite join_pure_x.
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
  let: COYO _ g h := c in fmap g h.

Program Instance Coyoneda_Functor (f : Type -> Type) : Functor (Coyoneda f) := {
  fmap := fun _ _ f x => let: COYO _ g h := x in COYO (f \o g) h
}.

Module CoyonedaLaws.

Include FunctorLaws.

Require Import FunctionalExtensionality.

Program Instance Coyoneda_FunctorLaws (f : Type -> Type) :
  FunctorLaws (Coyoneda f).
Obligation 1. by move=> [*]. Qed.
Obligation 2. by move=> [*]. Qed.

Theorem coyo_to `{FunctorLaws f} : forall a (x : f a),
  lowerCoyoneda (liftCoyoneda x) = x.
Proof.
  move=> a x.
  rewrite /lowerCoyoneda /liftCoyoneda.
  exact: fmap_id.
Qed.

Theorem coyo_lower_naturality `{FunctorLaws f} : forall a b (g : a -> b),
  fmap g \o lowerCoyoneda (f:=f) = lowerCoyoneda \o fmap g.
Proof.
  move=> a b k.
  extensionality x.
  move: x => [x g h] /=.
  exact: fmap_comp.
Qed.

Axiom coyo_parametricity : forall `{FunctorLaws f} a b (g : a -> b),
  COYO g = COYO id \o fmap g.

Theorem coyo_lift_naturality `{FunctorLaws f} : forall a b (g : a -> b),
  fmap g \o liftCoyoneda (f:=f) = liftCoyoneda \o fmap g.
Proof.
  move=> a b g.
  rewrite /liftCoyoneda.
  extensionality x.
  rewrite /=.
  recomp.
  congr (_ x).
  replace (g \o id) with g; last by [].
  exact: coyo_parametricity.
Qed.

Theorem coyo_from `{FunctorLaws f} : forall a (x : Coyoneda f a),
  liftCoyoneda (lowerCoyoneda x) = x.
Proof.
  move=> a [x g h].
  rewrite /lowerCoyoneda.
  recomp.
  by rewrite -coyo_lift_naturality.
Qed.

End CoyonedaLaws.
