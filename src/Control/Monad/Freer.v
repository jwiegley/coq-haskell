Require Import Hask.Prelude.
Require Import Hask.Control.Monad.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition Free (f : Type -> Type) (a : Type) :=
  forall r, (a -> r) -> (forall x, (x -> r) -> f x -> r) -> r.

Definition iter `{Functor f} `(phi : f a -> a) (fr : Free f a) : a :=
  fr _ id (fun _ k x => phi (fmap k x)).

Definition liftF {f : Type -> Type} {a : Type} (x : f a) : Free f a :=
  fun r p j => j a p x.

Definition uniter `(psi : Free f a -> a) : f a -> a :=
  psi \o liftF.

Definition retract `{Monad f} `(fr : Free f a) : f a :=
  fr _ pure (fun _ k x => x >>= k).

Definition hoistFree `(n : forall a, f a -> g a) `(fr : Free f b) :
  Free g b := fun r p j => fr _ p (fun _ k v => j _ k (n _ v)).

Definition foldFree `{Monad m} `(n : forall x, f x -> m x) `(fr : Free f a) :
  m a := fr _ pure (fun _ k x => join $ fmap k (n _ x)).

Definition foldFreeCPS `(n : forall x r, f x -> (x -> r) -> r)
  `(fr : Free f a) : forall r, (a -> r) -> r := fun r p =>
  fr r p (fun t k x => n t r x k).

Global Instance Free_Functor `{Functor f} : Functor (Free f) := {
  fmap := fun _ _ k fr => fun _ p j => fr _ (p \o k) j
}.

Global Instance Free_Applicative `{Functor f} : Applicative (Free f) := {
  pure := fun _ x => fun _ p j => p x;
  ap   := fun _ _ mf mx =>
            fun _ p j => mf _ (fun f => mx _ (fun x => p (f x)) j) j
}.

Global Instance Free_Monad `{Functor f} : Monad (Free f) := {
  join := fun _ mm => fun _ p j => mm _ (fun m => m _ p j) j
}.

Module FreeLaws.

Include MonadLaws.

Require Import FunctionalExtensionality.

Program Instance Free_FunctorLaws `{FunctorLaws f} : FunctorLaws (Free f).
Program Instance Free_ApplicativeLaws `{FunctorLaws f} :
  ApplicativeLaws (Free f).
Program Instance Free_MonadLaws `{FunctorLaws f} : MonadLaws (Free f).

Theorem retract_liftF_id `{MonadLaws f} : forall a,
  retract \o liftF = @id (f a).
Admitted.
(* Proof. *)
(*   move=> *. *)
(*   rewrite /retract /liftF. *)
(*   exact: join_fmap_pure. *)
(* Qed. *)

Theorem retract_distributes `{Monad f} `{MonadLaws f} : forall a (x y : Free f a),
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

(*
Axiom Free_parametricity : forall `{FunctorLaws f} a b (g : a -> b),
  Join (Pure \o g) = Join Pure \o fmap g.
*)

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

(*
Fixpoint to_free `(v : Free.Free f a) : Freer.Free f a :=
  match v with
  | Free.Pure x => fun _ p _ => p x
  | Free.Join r k x => fun _ p j => j _ (fun r => to_free (k r) p j) x
  end.

Definition from_free `(v : Freer.Free f a) : Free.Free f a :=
  v _ Pure (@Join f a).

Lemma from_to_free : forall `(x : Free.Free f a), from_free (to_free x) = x.
Proof.
  intros.
  unfold from_free.
  induction x; simpl.
    reflexivity.
  f_equal.
  extensionality r.
  rewrite H.
  reflexivity.
Qed.

Lemma free_ind :
  forall `{Functor f} {A} (P : Freer.Free f A -> Prop)
         (Hpure : forall (k : A), P (Pure k))
         (Hjoin : forall x (v : f x), P x -> P x)
         (x : Free f A), P x.
Proof.
  intros.
  destruct (x (Free.Free f A) Pure (@Join f A)).
  apply Hpure.
    apply Hpure.
  apply Hjoin.
Qed.

Lemma from_free_inj : forall `(x : Freer.Free f a) y,
  from_free x = from_free y -> x = y.
Proof.
Admitted.

Lemma to_from_free : forall `(x : Freer.Free f a), to_free (from_free x) = x.
Proof.
  intros.
  change (from_free (to_free (from_free x)) = from_free x).
  replace x with (from_free x).
  rewrite <- from_to_free.
  unfold to_free.

Lemma inside_out : forall (f : Free IO unit) x,
    f (IO_ unit) x
      (fun t k (v : IO t) =>
         match v with
         | PutStrLn s z => IOBind_ (putStrLn_ s) (k z)
         | Monitor  s z => IOBind_ (putStrLn_ s) (k z)
         end) =
    IOBind_ (x tt) (f (IO_ unit) IOReturn_
      (fun t k (v : IO t) =>
         match v with
         | PutStrLn s z => IOBind_ (putStrLn_ s) (k z)
         | Monitor  s z => IOBind_ (putStrLn_ s) (k z)
         end)).
Proof.
  intros.
  compute.
*)
