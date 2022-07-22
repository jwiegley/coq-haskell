Require Import Hask.Prelude.
Require Import Hask.Ltac.
Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.State.
Require Import Hask.Control.Monad.Trans.Class.

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
  s -> m (a * s)%type.

Definition getT  `{Applicative m} {s : Type}     : StateT s m s :=
  fun i => pure (i, i).
Definition getsT `{Applicative m} {s a : Type} f : StateT s m a :=
  fun s => pure (f s, s).
Definition putT  `{Applicative m} {s : Type} x   : StateT s m unit :=
  fun _ => pure (tt, x).

Definition modifyT `{Applicative m} {s : Type} (f : s -> s) : StateT s m unit :=
  fun i => pure (tt, f i).

#[export]
Program Instance StateT_Functor {s} `{Functor m} : Functor (StateT s m) := {
  fmap := fun A B f (x : StateT s m A) => fun st =>
    x st <&> first f
}.

Definition StateT_ap `{Monad m} {s : Type} {a b : Type}
  (f : StateT s m (a -> b)) (x : StateT s m a) : StateT s m b := fun st =>
  join (f st <&> fun z => match z with
    | (f', st') => x st' <&> first f'
    end).

#[export]
Program Instance StateT_Applicative `{Monad m} {s : Type} :
  Applicative (StateT s m) := {
  pure := fun _ x => fun st => pure (x, st);
  ap   := @StateT_ap m _ s
}.

Definition StateT_join `{Monad m} {s a : Type} (x : StateT s m (StateT s m a)) :
  StateT s m a := join \o fmap (curry apply) \o x.

#[export]
Program Instance StateT_Monad `{Monad m} {s : Type} : Monad (StateT s m) := {
  join := @StateT_join m _ s
}.

#[export]
Instance StateT_MonadTrans {s} : MonadTrans (StateT s) :=
{ lift := fun m _ _ A x s => fmap (fun k => (k, s)) x
}.

Definition liftStateT `{Monad m} `(x : State s a) : StateT s m a :=
  st <- getT ;
  let (a, st') := x st in
  putT st' ;;
  pure a.

Require Import FunctionalExtensionality.

Module StateTLaws.

Include MonadLaws.

Lemma first_id : forall a z, first (a:=a) (b:=a) (z:=z) id = id.
Proof.
  unfold first.
  intros a z.
  extensionality x.
  destruct x; auto.
Qed.

#[export]
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

#[export]
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

#[export]
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
