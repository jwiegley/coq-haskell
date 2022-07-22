(* Require Import Hask.Data.Functor.Identity. *)
Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.Base.
Require Import Hask.Control.Monad.Trans.State.
(* Require Import Hask.Control.Monad.Trans.Free. *)

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class StMC (m : Type -> Type) : Type := {
  StM : Type -> Type
}.
Arguments StM m {_} a.

Definition RunInBase m `{StMC m} b := forall a, m a -> b (StM m a).

Class MonadBaseControl b m `{MonadBase b m} `{StMC m} := {
  liftBaseWith : forall a, (RunInBase m b -> b a) -> m a;
  restoreM : forall a, StM m a -> m a
}.
Arguments liftBaseWith {b m _ _ _ _ _ _ a} _.
Arguments restoreM {b m _ _ _ _ _ _ a} _.

Class MonadBaseControlLaws b m `{MonadBaseControl b m} := {
  mbc_law_1 : forall a, liftBaseWith \o const \o pure[b] = @pure m _ a;
  mbc_law_2 : forall a (x : b a) r (f : a -> b r),
    liftBaseWith (const (x >>= f))
      = liftBaseWith (const x) >>= (liftBaseWith \o const \o f);
  mbc_law_3 : forall a (x : m a),
    liftBaseWith (fun runInBase => runInBase _ x) >>= restoreM = x
}.

Corollary mbc_law_1_x : forall b m `{MonadBaseControlLaws b m} a x,
  liftBaseWith (const (pure[b] x)) = @pure m _ a x.
Proof.
  intros.
  rewrite <- (@mbc_law_1 b m _ _ _ _ _ _ _).
  reflexivity.
Qed.

(* #[export] *)
(* Instance StMC_Identity : StMC Identity := { *)
(*   StM := id *)
(* }. *)

(* #[export] *)
(* Instance MonadBaseControl_Id_Id : *)
(*   MonadBaseControl Identity Identity := { *)
(*   liftBaseWith := fun _ runInBase => liftBase (runInBase (fun _ => pure)); *)
(*   restoreM := fun A => @id A *)
(* }. *)

(* #[export] *)
(* Program Instance MonadBaseControlLaws_Id_Id : *)
(*   MonadBaseControlLaws Identity Identity. *)

#[export]
Instance StMC_StateT s m `{StMC m} : StMC (StateT s m) := {
  StM := fun A => StM m (A * s)%type
}.

#[export]
Program Instance MonadBaseControl_StateT s `{MonadBaseControl b m} :
  MonadBaseControl b (StateT s m) := {
  liftBaseWith := fun _ f => fun st =>
    res <- liftBaseWith (fun runInBase : RunInBase m b =>
                           f (fun A k => runInBase _ (k st)));
    pure (res, st);
  restoreM := fun _ => const \o restoreM
}.

(*
#[export]
Instance FreeT_m_b {f : Type -> Type} {m b : Type -> Type}
         `{FunDep (Type -> Type) m b} :
  FunDep (FreeT f m) b.

#[export]
Instance MonadBase_FreeT `{Functor f} {m b : Type -> Type}
         `{B : MonadBase b m} : MonadBase b (FreeT f m) := {
  liftBase := fun _ x => fun _ p _ => liftBase x >>= p
}.

#[export]
Instance StMC_FreeT f m `{StMC m} : StMC (FreeT f m) := {
  StM := fun A => FreeF f A (FreeT f m (StM m A))
}.

Definition embedF `{Monad m} `{Functor f} {t}
           (k : m (FreeF f t (FreeT f m t))) : FreeT f m t :=
  fun r p j =>
    res <- k;
    match res : FreeF f t (FreeT f m t) with
    | Pure x => p x
    | Free x => j (m r) id (fmap (fun k => k r p j) x)
    end.

#[export]
Program Instance MonadBaseControl_FreeT `{Functor f} `{MonadBaseControl b m} :
  MonadBaseControl b (FreeT f m) := {

  liftBaseWith := fun a g =>
    fun r p j =>
      liftBaseWith
          (fun runInBase : RunInBase m b =>
             g (fun t k =>
                  runInBase _ (k _ (fun x : t => pure (Pure x))
                                   (fun u h (x : f u) =>
                                      pure (Free (fmap (embedF \o h) x))))))
        >>= p;

  restoreM := fun a (x : StM (FreeT f m) a) => embedF (restoreM x)
}.
*)

Require Import FunctionalExtensionality.

Module MonadBaseControlLaws.

Import MonadLaws.

#[export]
Program Instance MonadBaseControlLaws_StateT
        s `{MonadBaseControlLaws b m} `{@MonadLaws b H} `{@MonadLaws m H0} :
  MonadBaseControlLaws b (StateT s m).
Obligation 1.
  extensionality x.
  extensionality st.
  pose proof (@mbc_law_1_x b m _ _ _ _ _ _ _ a) as H9.
  unfold bind, comp, const in *.
  rewrite H9, fmap_pure_x, join_pure_x.
  reflexivity.
Qed.
Obligation 2.
  extensionality st.
  pose proof (@mbc_law_2 b m _ _ _ _ _ _ _) as H10.
  unfold StateT_join, bind, comp, Tuple.curry, Tuple.first,
         Prelude.apply, const in *.
  rewrite !H10, !fmap_comp_x, <- !join_fmap_fmap_x, !fmap_comp_x,
          <- !join_fmap_join_x, !fmap_comp_x.
  f_equal; f_equal.
  extensionality y.
  rewrite fmap_pure_x, join_pure_x.
  reflexivity.
Qed.
Obligation 3.
  pose proof (@mbc_law_3 b m _ _ _ _ _ _ _) as H10.
  unfold StateT_join, bind, comp, Tuple.curry, Tuple.first,
         Prelude.apply, const in *.
  extensionality st.
  rewrite fmap_comp_x, <- join_fmap_fmap_x, <- join_fmap_join_x, !fmap_comp_x.
  setoid_rewrite fmap_pure_x.
  setoid_rewrite join_pure_x.
  rewrite H10.
  reflexivity.
Qed.

(*
#[export]
Program Instance MonadBaseControlLaws_FreeT
        `{Functor f} `{MonadBaseControlLaws b m}
        `{@MonadLaws b H0} `{@MonadLaws m H1} :
  MonadBaseControlLaws b (FreeT f m).
Obligation 1.
  extensionality x.
  extensionality r.
  extensionality p.
  extensionality j.
  pose proof (@mbc_law_1_x b m _ _ _ _ _ _ _ a) as H9.
  unfold bind, comp, const in *.
  rewrite H9, fmap_pure_x, join_pure_x.
  reflexivity.
Qed.
Obligation 2.
  extensionality r'.
  extensionality p.
  extensionality j.
  pose proof (@mbc_law_2 b m _ _ _ _ _ _ _) as H10.
  unfold StateT_join, bind, comp, Tuple.curry, Tuple.first,
         Prelude.apply, const in *.
  rewrite H10, <- !join_fmap_fmap_x, !fmap_comp_x,
          <- !join_fmap_join_x, !fmap_comp_x.
  f_equal; f_equal.
Qed.
Obligation 3.
  pose proof (@mbc_law_3 b m _ _ _ _ _ _ _) as H10.
  unfold StateT_join, bind, comp, Tuple.curry, Tuple.first,
         Prelude.apply, const in *.
  extensionality r.
  extensionality p.
  extensionality j.
  rewrite <- join_fmap_fmap_x, <- join_fmap_join_x, !fmap_comp_x.
  setoid_rewrite fmap_pure_x.
  setoid_rewrite join_pure_x.
  rewrite H10.
  reflexivity.
Qed.
*)

End MonadBaseControlLaws.
