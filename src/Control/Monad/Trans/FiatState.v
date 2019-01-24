(* Require Import Hask.Prelude. *)
Require Import Hask.Ltac.
Require Import Hask.Control.Monad.
(* Require Import Hask.Control.Monad.Trans.Class. *)

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************
 * The StateT Monad transformer
 *)

Definition StateT (s : Type) (m : Type -> Type) (a : Type):=
  s -> m (s * a)%type.

Definition getT  `{Applicative m} {s : Type}     : StateT s m s :=
  fun i => pure (i, i).
Definition getsT `{Applicative m} {s a : Type} f : StateT s m a :=
  fun s => pure (s, f s).
Definition putT  `{Applicative m} {s : Type} x   : StateT s m unit :=
  fun _ => pure (x, tt).

Definition modifyT `{Applicative m} {s : Type} (f : s -> s) : StateT s m unit :=
  fun i => pure (f i, tt).

Definition StateT_ap `{Monad m} {s : Type} {a b : Type}
  (mf : StateT s m (a -> b)) (mx : StateT s m a) : StateT s m b := fun st =>
  p <- mf st;
  match p with
    (st', f) =>
      p <- mx st';
      match p with
        (st'', x) =>
          pure (st'', f x)
      end
  end.

Definition StateT_join `{Monad m} {s a : Type} (x : StateT s m (StateT s m a)) :
  StateT s m a := fun s =>
    p <- x s;
    match p with
      (s', x') => x' s'
    end.

(*
Module StateTLaws.

Require Import FunctionalExtensionality.

Include MonadLaws.

Lemma second_id : forall a z, second (a:=a) (b:=a) (z:=z) id = id.
Proof.
  unfold second.
  intros a z.
  extensionality x.
  destruct x; auto.
Qed.

Program Instance StateT_FunctorLaws {s} `{FunctorLaws m} :
  FunctorLaws (StateT s m).
Next Obligation. Admitted.
Next Obligation. Admitted.
(* Obligation 1. *)
(*   move=> x. *)
(*   extensionality st. *)
(*   rewrite first_id. *)
(*   replace (fun z : a * s => (z.1, z.2)) with (@id (a * s)%type); last first. *)
(*     by extensionality z; case z. *)
(*   by rewrite fmap_id. *)
(* Qed. *)
(* Obligation 2. *)
(*   rewrite /funcomp => x. *)
(*   extensionality st. *)
(*   rewrite fmap_comp_x /first. *)
(*   f_equal. *)
(*   extensionality y. *)
(*   by case: y. *)
(* Qed. *)

Program Instance StateT_Applicative `{MonadLaws m} {s : Type} :
  ApplicativeLaws (StateT s m).
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
(* Obligation 1. *)
(*   move=> x. *)
(*   extensionality st. *)
(*   rewrite /StateT_ap fmap_pure_x join_pure_x. *)
(*   set f := (X in fmap X). *)
(*   replace f with (@id (a * s)%type); last first. *)
(*     extensionality z. *)
(*     by case: z. *)
(*   by rewrite fmap_id. *)
(* Qed. *)
(* Obligation 2. *)
(*   extensionality st. *)
(*   rewrite /StateT_ap. *)
(*   set f := (X in join (fmap X _)). *)
(*   set g := (X in fmap f (join (fmap X _))). *)
(*   set h := (X in fmap g (join (fmap X _))). *)
(*   set i := (X in join (fmap X (u st))). *)
(*   rewrite -!join_fmap_fmap_x !fmap_comp_x fmap_pure_x *)
(*           join_pure_x -join_fmap_join_x. *)
(*   f_equal; rewrite !fmap_comp_x; f_equal. *)
(*   extensionality u'. *)
(*   case: u' => f' st'. *)
(*   rewrite /i -join_fmap_fmap_x. *)
(*   f_equal; rewrite !fmap_comp_x; f_equal. *)
(*   extensionality v'. *)
(*   case: v' => f'' st''. *)
(*   rewrite /f /first !fmap_comp_x; f_equal. *)
(*   extensionality w'. *)
(*   case: w' => f''' st'''. *)
(*   by rewrite /funcomp. *)
(* Qed. *)
(* Obligation 3. *)
(*   extensionality st. *)
(*   by rewrite /StateT_ap fmap_pure_x join_pure_x fmap_pure_x. *)
(* Qed. *)
(* Obligation 4. *)
(*   extensionality st. *)
(*   rewrite /StateT_ap fmap_pure_x. *)
(*   set f := (X in join (fmap X _)). *)
(*   set g := (X in _ = join (pure (fmap X _))). *)
(*   rewrite join_pure_x. *)
(*   recomp; f_equal. *)
(*   extensionality z. *)
(*   have H1 : pure \o g = f. *)
(*     rewrite /f /g /funcomp. *)
(*     extensionality x. *)
(*     case: x => f' st'. *)
(*     by rewrite fmap_pure_x. *)
(*   by rewrite -H1 /funcomp -fmap_comp_x join_fmap_pure_x. *)
(* Qed. *)
(* Obligation 5. *)
(*   move=> x. *)
(*   extensionality st. *)
(*   rewrite /StateT_ap fmap_pure_x join_pure_x. *)
(*   f_equal. *)
(* Qed. *)

Program Instance StateT_Monad `{MonadLaws m} {s : Type} :
  MonadLaws (StateT s m).
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
(* Obligation 1. *)
(*   move=> f. *)
(*   extensionality st. *)
(*   rewrite /StateT_join /= -!ap_fmap -ap_comp !ap_homo *)
(*           !ap_fmap -join_fmap_fmap_x -join_fmap_join_x fmap_comp_x. *)
(*   f_equal. *)
(*   rewrite fmap_comp_x. *)
(*   f_equal. *)
(*   extensionality y. *)
(*   by case: y => f' st'. *)
(* Qed. *)
(* Obligation 2. *)
(*   move=> f. *)
(*   extensionality st. *)
(*   rewrite /StateT_join /= fmap_comp_x /curry /apply /first. *)
(*   set h := (X in fmap X _). *)
(*   replace h with (@pure m _ (a * s)%type); last first. *)
(*     extensionality z. *)
(*     by case: z. *)
(*   by rewrite join_fmap_pure_x. *)
(* Qed. *)
(* Obligation 3. *)
(*   move=> f. *)
(*   extensionality st. *)
(*   by rewrite /StateT_join /= fmap_pure_x join_pure_x. *)
(* Qed. *)
(* Obligation 4. *)
(*   move=> x. *)
(*   extensionality st. *)
(*   rewrite /StateT_join /= -join_fmap_fmap_x. *)
(*   f_equal; rewrite !fmap_comp_x; f_equal. *)
(*   extensionality y. *)
(*   by case: y. *)
(* Qed. *)

End StateTLaws.
*)

(* Instance Tuple_Functor {S} : Functor (fun a => (S * a)%type) | 9 := { *)
(*   fmap := fun _ _ f p => (fst p, f (snd p)) *)
(* }. *)

Instance StateT_Functor `{Functor m} {S} : Functor (StateT S m) := {
  fmap := fun _ _ f x => fun s =>
    x s <&> fun p =>
              match p with
                (s', a) => (s', f a)
              end
}.

Instance StateT_Applicative `{Monad m} {S} : Applicative (StateT S m) := {
  pure := fun _ x => fun s => pure (s, x);
  ap := @StateT_ap _ _ _
}.

Instance StateT_Monad `{Monad m} {S} : Monad (StateT S m) := {
  join := @StateT_join _ _ _
}.

Module StateTLaws.

Import MonadLaws.
Require Import FunctionalExtensionality.

(* Program Instance Tuple_FunctorLaws {S} : FunctorLaws (fun a => (S * a)%type). *)
(* Obligation 1. *)
(*   extensionality p. *)
(*   destruct p; reflexivity. *)
(* Qed. *)

(* Program Instance StateT_FunctorLaws `{FunctorLaws m} {S} : *)
(*   FunctorLaws (StateT S m) := *)
(*   @Compose_FunctorLaws _ Impl_Functor Impl_FunctorLaws *)
(*     _ _ (@Compose_FunctorLaws m _ _ _ _ (@Tuple_FunctorLaws S)). *)

(*
Program Instance StateT_ApplicativeLaws `{MonadLaws m} {S} :
  ApplicativeLaws (StateT S m).
Obligation 1.
  extensionality x.
  extensionality st.
  unfold StateT_ap, StateT_join, id; simpl.
  rewrite fmap_pure_x, join_pure_x.
  unfold second; simpl.
  setoid_rewrite fst_snd.
  setoid_rewrite <- surjective_pairing.
  rewrite fmap_id.
  reflexivity.
Qed.
Obligation 2.
Abort.

Program Instance StateT_MonadLaws `{MonadLaws m} {S} :
  MonadLaws (StateT S m).
*)

End StateTLaws.

(*
Require Import Hask.Control.Monad.State.

Definition liftStateT `{Monad m} `(x : State s a) : StateT s m a :=
  st <- getT ;
  let (a, st') := x st in
  putT st' ;;
  pure a.
*)