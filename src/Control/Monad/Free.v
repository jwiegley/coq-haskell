Require Import Hask.Prelude.
Require Import Hask.Control.Monad.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.
Set Asymmetric Patterns.

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

Definition liftF {f : Type -> Type} {a : Type} : f a -> Free f a := Join Pure.

Definition uniter `{Functor f} `(psi : Free f a -> a) : f a -> a :=
  psi \o liftF.

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
  match n with
  | O => Pure None
  | S n' =>
    match fr with
    | Pure x => Pure (Some x)
    | Join _ g h => Join (cutoff n \o g) h
    end
  end.

(* jww (2015-06-02): With universe polymorphism this should work fine. *)
(* Definition wrap {f : Type -> Type} {a : Type} : *)
(*   f (Free f a) -> Free f a := Join id. *)

Definition Free_bind `(k : a -> Free f b) : Free f a -> Free f b :=
  fun x0 => let fix go x := match x with
    | Pure a => k a
    | Join _ g h => Join (go \o g) h
    end in
  go x0.

#[export]
Program Instance Free_Functor `{Functor f} : Functor (Free f) := {
  fmap := fun _ _ k => Free_bind (Pure \o k)
}.

#[export]
Program Instance Free_Applicative `{Functor f} :
  Applicative (Free f) := {
  pure := fun _ => Pure;
  ap   := fun _ _ mf mx => Free_bind (flip fmap mx) mf
}.

#[export]
Program Instance Free_Monad `{Functor f} : Monad (Free f) := {
  join := fun _ => Free_bind id
}.

(*
Require Import FunctionalExtensionality.

Module FreeLaws.

Include MonadLaws.

Ltac reduce_free H :=
  unfold id, comp, flip;
  try extensionality XX;
  simpl; auto;
  try match goal with
  | [ HF : Free _ _ |- _ ] =>
      induction HF as [|? ? H ?]; simpl; auto
  end;
  try f_equal;
  try apply f_equal2; auto;
  try extensionality YY;
  try apply H.

#[export]
Program Instance Free_FunctorLaws `{FunctorLaws f} : FunctorLaws (Free f).
Obligation 1. reduce_free IHx. Qed.
Obligation 2. reduce_free IHx. Qed.

#[export]
Program Instance Free_ApplicativeLaws `{FunctorLaws f} :
  ApplicativeLaws (Free f).
Obligation 1. reduce_free IHx. Qed.
Obligation 2.
  induction u as [?|? ? IHu ?].
    induction v as [?|? ? IHv ?]; simpl.
      reduce_free IHw.
    reduce_free IHv.
  reduce_free IHu.
Qed.

#[export]
Program Instance Free_MonadLaws `{FunctorLaws f} : MonadLaws (Free f).
Obligation 1. reduce_free IHx. Qed.
Obligation 2. reduce_free IHx. Qed.
Obligation 4. reduce_free IHx. Qed.

Theorem retract_liftF_id `{MonadLaws f} : forall a,
  retract \o liftF = @id (f a).
Proof.
  intros.
  unfold retract, liftF, comp.
  apply join_fmap_pure.
Qed.

Theorem retract_distributes `{MonadLaws f} : forall a (x y : Free f a),
  retract (x >> y) = (retract x >> retract y).
Admitted.
(* Proof. *)
(*   move=> ?. *)
(*   elim=> [?|? ? IHx ?] y; rewrite /bind /=. *)
(*     by rewrite -ap_fmap ap_homo join_pure_x. *)
(*   rewrite -join_fmap_fmap_x fmap_comp_x *)
(*           -join_fmap_join_x fmap_comp_x. *)
(*   congr (join (fmap _ _)). *)
(*   extensionality x. *)
(*   exact: IHx. *)
(* Qed. *)

Theorem retract_naturality `{MonadLaws f} : forall a b (g : a -> b),
  fmap g \o retract (f:=f) = retract \o fmap g.
Admitted.
(* Proof. *)
(*   move=> a b g x. *)
(*   rewrite /=. *)
(*   elim: x => [?|? ? IHx ?] /=. *)
(*     by rewrite fmap_pure_x. *)
(*   rewrite -join_fmap_fmap_x fmap_comp_x. *)
(*   congr (join (fmap _ _)). *)
(*   extensionality y => /=. *)
(*   exact: IHx. *)
(* Qed. *)

Axiom Free_parametricity : forall `{FunctorLaws f} a b (g : a -> b),
  Join (Pure \o g) = Join Pure \o fmap g.

Theorem liftF_naturality `{FunctorLaws f} : forall a b (g : a -> b),
  fmap g \o liftF (f:=f) = liftF \o fmap g.
Admitted.
(* Proof. *)
(*   move=> a b g x. *)
(*   rewrite /= /liftF. *)
(*   have ->: ([eta Free_bind (Pure \o g)] \o Pure) = Pure \o g. *)
(*     move=> ?. *)
(*     extensionality y. *)
(*     by rewrite /funcomp /Free_bind. *)
(*   exact: Free_parametricity. *)
(* Qed. *)

Corollary liftF_naturality_x `{FunctorLaws f} : forall a b (g : a -> b) x,
  fmap g (liftF x) = liftF (fmap g x).
Proof.
  intros.
  replace ((fmap[Free f] g) (liftF x)) with (((fmap[Free f] g) \o liftF) x).
    rewrite liftF_naturality.
    reflexivity.
  reflexivity.
Qed.

Theorem uniter_iter_id `{MonadLaws f} : forall a,
  uniter \o iter = @id (f a -> a).
Admitted.
(* Proof. *)
(*   move=> * x. *)
(*   extensionality z. *)
(*   rewrite /uniter /=. *)
(*   have ->: iter x \o Pure = id by []. *)
(*   by rewrite fmap_id. *)
(* Qed. *)

(*
Theorem iter_uniter_id `{MonadLaws f} : forall a,
  iter \o uniter = @id (Free f a -> a).
Proof.
  move=> a x.
  extensionality z.
  rewrite /uniter /=.
  elim: z => /= [?|? ? IHz ?].
    (* _a_ = x (Pure _a_) *)
    (* This is true by parametricity. *)
  move/functional_extensionality in IHz.
  rewrite -liftF_naturality_x.
  rewrite /funcomp IHz /= /funcomp.
  congr (x (Join _ _)).
  extensionality y.
  rewrite /Free_bind.
  (* Pure (x (_f_ y)) = _f_ y *)
  (* This is false if _f_ y returns Join. *)
*)

End FreeLaws.
*)

CoInductive CoFree (h : Type -> Type) (a : Type) :=
  CoF : a -> forall x, (x -> CoFree h a) -> h x -> CoFree h a.

Arguments CoF {h a} _ {x} _ _.

CoFixpoint unfold `(k : b -> a * f b) (z : b) : CoFree f a :=
  match k z with (x, j) => CoF x (unfold k) j end.

CoFixpoint CoFree_map {h} `(f : a -> b) (c : CoFree h a) :
  CoFree h b :=
  match c with CoF x s g h => CoF (f x) (CoFree_map f \o g) h end.

#[export]
Program Instance CoFree_Functor `{Functor h} : Functor (CoFree h) := {
  fmap := fun _ _ => CoFree_map
}.

Module CoFreeLaws.

Include FunctorLaws.

(*
#[export]
Program Instance CoFree_FunctorLaws `{FunctorLaws h} : FunctorLaws (CoFree h).
Obligation 1.
  move=> x.
  destruct x.
Obligation 2.
  move=> x.
  destruct x.
*)

End CoFreeLaws.
