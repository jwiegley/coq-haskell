Require Import Hask.Prelude.
Require Import Hask.Control.Monad.

Generalizable All Variables.

Inductive Free (f : Type -> Type) (a : Type) :=
  | Pure : a -> Free f a
  | Join : forall x, (x -> Free f a) -> f x -> Free f a.

Arguments Pure {f a} _.
Arguments Join {f a x} _ _.

Fixpoint iter `{Functor f} `(phi : f a -> a) (fr : Free f a) : a :=
  match fr with
    | Pure x => x
    | Join _ g h => phi $ fmap (iter phi \o g) h
  end.

Definition liftF {f : Type -> Type} {a : Type} : f a -> Free f a :=
  Join Pure.

Fixpoint retract `{Monad f} `(fr : Free f a) : f a :=
  match fr with
    | Pure x => pure x
    | Join _ g h => h >>= (retract \o g)
  end.

Fixpoint hoistFree `(n : forall a, f a -> g a) `(fr : Free f b) :
  Free g b :=
  match fr with
  | Pure x => Pure x
  | Join _ g h => Join (hoistFree n \o g) (n _ h)
  end.

Fixpoint foldFree `{Monad m} `(n : forall x, f x -> m x) `(fr : Free f a) :
  m a :=
  match fr with
  | Pure x => pure x
  | Join _ g h => join $ fmap (foldFree n \o g) (n _ h)
  end.

Fixpoint cutoff (n : nat) `(fr : Free f a) : Free f (option a) :=
  if n isn't S n' then Pure None else
  match fr with
  | Pure x => Pure (Some x)
  | Join _ g h => Join (cutoff n \o g) h
  end.

(* CoFixpoint unfold `(k : b -> a + f b) (z : b) : Free f a := *)
(*   match k z with *)
(*   | inl x => Pure x *)
(*   | inr j => Join (unfold k) j *)
(*   end. *)

(* jww (2015-06-02): With universe polymorphism this should work fine. *)
(* Definition wrap {f : Type -> Type} {a : Type} : *)
(*   f (Free f a) -> Free f a := Join id. *)

Definition Free_bind `(k : a -> Free f b) : Free f a -> Free f b :=
  fun x0 => let fix go x := match x with
    | Pure a => k a
    | Join _ g h => Join (go \o g) h
    end in
  go x0.

Program Instance Free_Functor `{Functor f} : Functor (Free f) := {
  fmap := fun _ _ k => Free_bind (Pure \o k)
}.

Program Instance Free_Applicative `{Functor f} : Applicative (Free f) := {
  pure := fun _ => Pure;
  ap   := fun _ _ mf mx => Free_bind (flip fmap mx) mf
}.

Program Instance Free_Monad `{Functor f} : Monad (Free f) := {
  join := fun _ => Free_bind id
}.

Module FreeLaws.

Include MonadLaws.

Require Import FunctionalExtensionality.

Ltac reduce_free H :=
  try elim=> //= [? ? H ?];
  congr (Join _ _);
  extensionality YY;
  exact: H.

Program Instance Free_FunctorLaws `{FunctorLaws f} : FunctorLaws (Free f).
Obligation 1. by reduce_free IHx. Qed.
Obligation 2. by reduce_free IHx. Qed.

Program Instance Free_ApplicativeLaws `{FunctorLaws f} :
  ApplicativeLaws (Free f).
Obligation 1. by reduce_free IHx. Qed.
Obligation 2.
  elim: u => /= [?|? ? IHu ?].
    elim: v => /= [?|? ? IHv ?].
      move: w.
      by reduce_free IHw.
    by reduce_free IHv.
  by reduce_free IHu.
Qed.

Program Instance Free_MonadLaws `{FunctorLaws f} : MonadLaws (Free f).
Obligation 1. by reduce_free IHx. Qed.
Obligation 2. by reduce_free IHx. Qed.
Obligation 4. by reduce_free IHx. Qed.

Theorem retract_liftF_id `{MonadLaws f} : forall a,
  retract \o liftF =1 @id (f a).
Proof.
  move=> *.
  rewrite /retract /liftF.
  exact: join_fmap_pure.
Qed.

Theorem retract_distributes `{MonadLaws f} : forall a (x y : Free f a),
  retract (x >> y) = retract x >> retract y.
Proof.
  move=> ?.
  elim=> [?|? ? IHx ?] y; rewrite /bind /=.
    by rewrite -ap_fmap ap_homo join_pure_x.
  rewrite -join_fmap_fmap_x fmap_comp_x
          -join_fmap_join_x fmap_comp_x.
  congr (join (fmap _ _)).
  extensionality x.
  exact: IHx.
Qed.

Theorem retract_naturality `{MonadLaws f} : forall a b (g : a -> b),
  fmap g \o retract (f:=f) =1 retract \o fmap g.
Proof.
  move=> a b g x.
  rewrite /=.
  elim: x => [?|? ? IHx ?] /=.
    by rewrite fmap_pure_x.
  rewrite -join_fmap_fmap_x fmap_comp_x.
  congr (join (fmap _ _)).
  extensionality y => /=.
  exact: IHx.
Qed.

Axiom Free_parametricity : forall `{FunctorLaws f} a b (g : a -> b),
  Join (Pure \o g) =1 Join Pure \o fmap g.

Theorem liftF_naturality `{FunctorLaws f} : forall a b (g : a -> b),
  fmap g \o liftF (f:=f) =1 liftF \o fmap g.
Proof.
  move=> a b g x.
  rewrite /= /liftF.
  have ->: ([eta Free_bind (Pure \o g)] \o Pure) = Pure \o g.
    move=> ?.
    extensionality y.
    by rewrite /funcomp /Free_bind.
  exact: Free_parametricity.
Qed.

End FreeLaws.
