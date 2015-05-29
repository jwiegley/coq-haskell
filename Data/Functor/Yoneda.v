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
