Require Export Cont.
Require Export EitherT.
Require Export Trans.
Require Category.

(* A type-wrapper is not strictly necessary here, since the Functor,
   Applicative and Monad behaviors are all directly based on Cont.  In Haskell
   it is needed, so we match that behavior here, to prove that nothing is
   violated owing to the wrapping.
*)
Inductive Source (M : Type -> Type) (R : Type) (A : Type) : Type :=
  Source_ : Cont (R -> EitherT R M R) A -> Source M R A.

Definition Source_map {M : Type -> Type} `{Functor M} {R X Y}
  (f : X -> Y) (x : Source M R X) : Source M R Y :=
  match x with Source_ k => Source_ M R Y (fmap f k) end.

#[export]
Instance Source_Functor {M : Type -> Type} `{Functor M} {R}
  : Functor (Source M R) :=
{ fmap := @Source_map M _ R
}.
Proof.
  - (* fun_identity *) intros. extensionality x.
    unfold Source_map.
    destruct x.
    unfold id.
    f_equal. simpl.
    unfold Cont_map.
    destruct c.
    f_equal.
  - (* fun_composition *) intros. extensionality x.
    unfold Source_map.
    destruct x. simpl.
    unfold compose, Cont_map.
    f_equal.
    destruct c.
    f_equal.
Defined.

Definition Source_apply {M : Type -> Type} `{Applicative M}
  {R X Y} (f : Source M R (X -> Y)) (x : Source M R X) : Source M R Y :=
  match f with
    Source_ k => match x with
      Source_ j => Source_ M R Y (ap k j)
    end
  end.

#[export]
Instance Source_Applicative {M : Type -> Type} `{Applicative M}
  {R} : Applicative (Source M R) :=
{ is_functor := Source_Functor
; pure := fun A x => Source_ M R A (pure x)
; ap := @Source_apply M _ R
}.
Proof.
  - (* app_identity *)
    intros. extensionality x.
    destruct x.
    unfold id, Source_apply.
    f_equal. simpl.
    apply (@app_identity_x _ Cont_Applicative).

  - (* app_composition *)
    intros.
    unfold Source_apply.
    destruct u. destruct v. destruct w.
    f_equal.
    apply app_composition.

  - (* app_homomorphism *)
    intros.
    unfold Source_apply.
    f_equal.

  - (* app_interchange *)
    intros.
    unfold Source_apply.
    destruct u.
    f_equal.
    apply app_interchange.

  - (* app_fmap_unit *)
    intros. extensionality x.
    unfold Source_apply.
    destruct x. simpl.
    f_equal.
    unfold Cont_map.
    destruct c.
    f_equal.
Defined.

Definition getSource {M : Type -> Type} {R X} (x : Source M R X)
  : Cont (R -> EitherT R M R) X :=
  match x with Source_ k => k end.

Definition Source_join {M : Type -> Type} `{Monad M}
  {R X} : Source M R (Source M R X) -> Source M R X :=
  Source_ M R X ∘ join ∘ fmap getSource ∘ getSource.

#[export]
Program Instance Source_Monad {M : Type -> Type} `{Monad M} {R}
  : Monad (Source M R) :=
{ is_applicative := Source_Applicative
; join := fun _ => Source_join
}.
Obligation 1. (* monad_law_1 *)
  intros. extensionality x. simpl.
  unfold Source_join, Source_map, id, compose.
  destruct x.
  destruct c. simpl.
  unfold compose, flip.
  repeat f_equal.
  extensionality p. f_equal.
  extensionality q. f_equal.
  destruct q.
  destruct c.
  reflexivity.
Qed.
Obligation 2. (* monad_law_2 *)
  intros. extensionality x. simpl.
  unfold Source_join, Source_map, id, compose.
  destruct x.
  f_equal. simpl.
  pose proof (@fun_composition_x _ (@Cont_Functor (R -> EitherT R M R))).
  simpl in H0.
  rewrite H0.
  pose proof (@monad_law_2_x _ (@Cont_Monad (R -> EitherT R M R))).
  simpl in H1.
  unfold compose. simpl.
  apply H1.
Qed.
Obligation 3. (* monad_law_3 *)
  intros. extensionality x. simpl.
  unfold Source_join, id, compose.
  destruct x.
  f_equal. simpl.
  unfold compose.
  destruct c.
  f_equal.
Qed.
Obligation 4. (* monad_law_4 *)
  intros. extensionality x. simpl.
  unfold Source_join, Source_map, compose.
  destruct x.
  destruct c.
  f_equal. simpl.
  f_equal.
  extensionality p.
  extensionality q.
  unfold compose.
  f_equal.
  extensionality r.
  extensionality s.
  destruct r.
  destruct c.
  reflexivity.
Admitted.

Definition source {M : Type -> Type} `{Monad M} {R A}
   (await : R -> (R -> A -> EitherT R M R) -> EitherT R M R)
  : Source M R A :=
  Source_ M R A (Cont_ (R -> EitherT R M R) A (flip await ∘ flip)).

Theorem source_distributes
  : forall {M : Type -> Type} `{Monad M} {R A}
    (m : EitherT R M A) (f : A -> EitherT R M A),
  source (fun (r : R) (yield : R -> A -> EitherT R M R) =>
            m >>= yield r)
    >>= (fun x : A =>
           source (fun (r : R) (yield : R -> A -> EitherT R M R) =>
                     f x >>= yield r)) =
  source (fun (r : R) (yield : R -> A -> EitherT R M R) =>
           m >>= f >>= yield r).
Admitted.
(*
Proof.
  intros.
  unfold bind, flip.
  simpl join.
  simpl fmap.
  unfold source, flip, compose.
  unfold Source_join, compose.
  simpl join. simpl.
  unfold compose, flip. simpl.
  f_equal. f_equal.
  extensionality p. extensionality q.
  pose (@monad_law_4_x (EitherT R M) EitherT_Monad).
  simpl in e. rewrite <- e. clear e.
  pose (@monad_law_1_x (EitherT R M) EitherT_Monad).
  simpl in e. rewrite <- e. clear e.
  f_equal.
  pose (@fun_composition_x (EitherT R M) EitherT_Functor).
  simpl in e. repeat (rewrite e). clear e.
  f_equal.
Qed.
*)

#[export]
Instance Source_MonadTrans {M : Type -> Type} `{Monad M} {R}
  : @MonadTrans (fun N => Source N R) M _ Source_Monad :=
{ lift := fun _ m => source (fun r yield => lift m >>= yield r)
}.
Proof.
  - (* trans_law_1 *) intros.
    unfold source. simpl pure.
    extensionality e. unfold compose at 1.
    f_equal. f_equal.
    unfold flip. unfold compose at 1.
    unfold bind.
    rewrite trans_law_1_x.
    pose proof app_fmap_compose_x.
    specialize (H0 (EitherT R M) is_applicative A (EitherT R M R)).
    simpl join.
    simpl pure.
    simpl pure in H0.
    extensionality p. extensionality q.
    rewrite <- H0.
    pose proof monad_law_3_x.
    specialize (H1 (EitherT R M) EitherT_Monad R (p e q)).
    simpl join in H1.
    simpl pure in H1.
    assumption.

  - (* trans_law_2 *) intros.
    pose (@trans_law_2 (EitherT R) M _ _ _ A).
    unfold compose. rewrite e.
    rewrite source_distributes.
    reflexivity.
Defined.

(*
Require Export Category.

(* Src is the category of simple-conduit Sources:

   Objects are sources
   Morphisms are the source homomorphisms (aka conduits)

   Identity is just simple identity
   Composition is just simple composition, since monadic folds
     are simply functions modulo type wrapping.

   Thus, the proof are extremely trivial and follow immediately from the
   definitions.

   Another way to say it is that since, by naturality, the image of a functor
   is always a sub-category in its codomain, and since Sources are functors,
   they must also then be categories.
*)
#[export]
Instance Src {M : Type -> Type} `{Monad M} {R}
  : Category (sigT (Source M R))
             (fun dom ran => projT1 dom → projT1 ran) :=
{ id      := fun _ x => id x
; compose := fun _ _ _ f g x => f (g x)
}.
Proof.
  (* The proofs of all of these follow trivially from their definitions. *)
  - (* right_identity *)   crush.
  - (* left_identity *)    crush.
  - (* comp_assoc *)       crush.
Defined.
*)
