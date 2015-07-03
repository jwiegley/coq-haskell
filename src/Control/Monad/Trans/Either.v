Require Import Hask.Prelude.
Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.Trans.Class.
Require Import Hask.Control.Monad.Morph.

Definition EitherT (X : Type) (M : Type -> Type) (Y : Type) : Type :=
  M (Either X Y).

Definition EitherT_map {E M} `{Functor M} {X Y}
  (f : X -> Y) (x : EitherT E M X) : EitherT E M Y :=
  (fmap[M] (fmap[Either E] f)) x.

Instance EitherT_Functor {E M} `{Functor M} : Functor (EitherT E M) :=
{ fmap := fun _ _ => EitherT_map
}.
(* jww (2015-06-17): NYI
Proof.
  - (* fun_identity *)
    intros.
    extensionality x.
    unfold EitherT_map.
    destruct x.
    repeat (rewrite fun_identity).
    unfold id.
    reflexivity.

  - (* fun_composition *)
    intros.
    extensionality x.
    unfold EitherT_map.
    destruct x.
    repeat (rewrite <- fun_composition).
    unfold compose.
    reflexivity.
Defined.
*)

Definition EitherT_pure {E M} `{Applicative M} {X}
  : X -> EitherT E M X := pure/M \o pure/(Either E).

Definition EitherT_apply {E M} `{Applicative M} {X Y}
  (mf : EitherT E M (X -> Y)) (mx : EitherT E M X) : EitherT E M Y :=
  (ap[M] ((fmap[M] ap) mf)) mx.

Instance EitherT_Applicative {E M} `{Applicative M}
  : Applicative (EitherT E M) :=
{ pure := fun _   => EitherT_pure
; ap   := fun _ _ => EitherT_apply
}.
(* jww (2015-06-17): NYI
Proof.
  - (* app_identity *) intros. extensionality x.
    unfold EitherT_apply, EitherT_pure.
    destruct x.
    unfold id, compose.
    f_equal.
    apply (@app_identity_x (fun X => fobj (fobj X))
          (Applicative_Compose M (Either E))).

  - (* app_composition *) intros.
    unfold EitherT_apply, EitherT_pure.
    destruct u. destruct v. destruct w.
    unfold compose.
    f_equal.
    apply (@app_composition (fun X => fobj (fobj X))
          (Applicative_Compose M (Either E))).

  - (* app_homomorphism *) intros.
    unfold EitherT_apply, EitherT_pure. f_equal.
    unfold compose.
    f_equal.
    apply (@app_homomorphism (fun X => fobj (fobj X))
          (Applicative_Compose M (Either E))).

  - (* app_interchange *) intros.
    unfold EitherT_apply, EitherT_pure.
    destruct u.
    unfold compose.
    f_equal.
    apply (@app_interchange (fun X => fobj (fobj X))
          (Applicative_Compose M (Either E))).

  - (* app_fmap_unit *) intros.
    unfold EitherT_apply, EitherT_pure.
    unfold compose.
    f_equal.
    rewrite_app_homomorphisms.
    reflexivity.
Defined.
*)

Definition EitherT_join {E M} `{Monad M} {X} (x : EitherT E M (EitherT E M X)) :
  EitherT E M X :=
  join (fmap (fun y => match y with
                | Left e => pure (Left e)
                | Right mx' => mx'
                end) x).

Instance EitherT_Monad {E M} `{Monad M} : Monad (EitherT E M) :=
{ join := fun _ => EitherT_join
}.
(* jww (2015-06-17): NYI
Proof.
  - (* monad_law_1 *) intros. extensionality x. simpl.
    unfold compose, EitherT_join.
    destruct x. simpl.
    f_equal. simpl.
    unfold Either_map.
    repeat (rewrite fun_composition_x).
    unfold compose.
    rewrite <- monad_law_4_x.
    unfold compose.
    rewrite <- monad_law_1_x.
    repeat (rewrite fun_composition_x).
    repeat f_equal.
    unfold compose.
    extensionality x. destruct x.
      rewrite <- app_fmap_unit.
        rewrite app_homomorphism.
        rewrite monad_law_3_x.
        reflexivity.
      destruct e. reflexivity.

  - (* monad_law_2 *) intros. extensionality x. simpl.
    unfold compose, EitherT_join, EitherT_pure.
    simpl. destruct x.
    unfold EitherT_map, id.
    simpl. f_equal.
    rewrite fun_composition_x.
    unfold compose, Either_map.
    rewrite <- uncompose with (f := join).
      assert ((fun x : Either E X =>
                 match
                   match x with
                   | Left e => Left E (EitherT E M X) e
                   | Right x' =>
                       Right E (EitherT E M X)
                         (EitherT_ E M X ((pure/M) (Right E X x')))
                   end
                 with
                 | Left e => (pure/M) (Left E X e)
                 | Right (EitherT_ mx') => mx'
                 end) = (@pure M _ (Either E X))).
        extensionality x. destruct x; reflexivity. rewrite H0. clear H0.
    apply monad_law_2_x.
    assumption.

  - (* monad_law_3 *) intros. extensionality x. simpl.
    unfold compose, EitherT_join, EitherT_pure.
    simpl. destruct x.
    unfold compose, id. f_equal.
    rewrite <- app_fmap_compose_x.
    rewrite <- uncompose with (f := join).
      rewrite monad_law_3. reflexivity.
      assumption.

  - (* monad_law_4 *) intros. extensionality x. simpl.
    unfold compose, EitherT_join, EitherT_map.
    simpl. destruct x. f_equal.
    rewrite <- monad_law_4_x.
    f_equal.
    repeat (rewrite fun_composition_x).
    unfold compose.
    f_equal. extensionality x.
    destruct x; simpl.
      unfold Either_map. simpl.
      rewrite <- app_fmap_compose_x. reflexivity.
      destruct e. reflexivity.
Defined.
*)

Instance EitherT_MonadTrans {E} : MonadTrans (EitherT E) :=
{ lift := fun m _ _ A => fmap Right
}.
(* jww (2015-06-17): NYI
Proof.
  - (* trans_law_1 *) intros. extensionality x.
    repeat (rewrite <- comp_assoc).
    rewrite <- app_fmap_compose.
    reflexivity.
  - (* trans_law_2 *) intros.
    unfold bind, compose. simpl.
    repeat (rewrite fun_composition_x).
    unfold compose. simpl. f_equal.
    rewrite <- monad_law_4_x. f_equal.
    rewrite fun_composition_x.
    reflexivity.
Defined.
*)

Program Instance EitherT_MFunctor {E} : MFunctor (EitherT E) :=
{ hoist := fun M N _ _ A nat => nat (Either E A)
}.
(* jww (2015-06-17):  NYI
Proof.
  - (* hoist_law_1 *) intros. extensionality x.
    destruct x. subst.
    reflexivity.
  - (* hoist_law_2 *) intros. extensionality x.
    destruct x.
    unfold compose.
    reflexivity.
Defined.
*)

(*
Instance EitherT_MMonad {E}
  `{Monad (Either E)}
  : MMonad (EitherT E) EitherT_MFunctor EitherT_MonadTrans :=
{ embed := fun M N nd tnd A f m =>
    EitherT_ E N A (match m with
      EitherT_ m' => match f (Either E A) m' with
        EitherT_ m'' =>
          fmap (fun x => match x with
            | Left e => Left E A e
            | Right (Left e) => Left E A e
            | Right (Right x) => Right E A x
            end) m''
      end
    end)
}.
Proof.
  - (* embed_law_1 *) intros. extensionality x.
    destruct x.
    unfold id.
    f_equal.
    inversion td.
  - (* embed_law_2 *) intros.
  - (* embed_law_3 *) intros.
Defined.
*)