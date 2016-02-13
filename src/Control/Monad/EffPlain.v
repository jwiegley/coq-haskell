Require Import
  Hask.Control.Monad
  Hask.Data.Maybe
  Coq.Lists.List.

Generalizable All Variables.

Import ListNotations.

Definition Effect := (Type -> Type) -> Type.

Inductive Effects (m : Type -> Type) : list Effect -> Type :=
  | NilE : Effects m []
  | ConsE effects : forall effect : Effect,
      effect m -> Effects m effects -> Effects m (effect :: effects).

Arguments ConsE : default implicits.

Definition combine `(e : effect m) `(xs : Effects m effects) :
  Effects m (effect :: effects) := ConsE _ e xs.

Infix ".:" := combine (at level 48, right associativity).

Class Handles (fs : list Effect) (effect : Effect) := {
  getEffect : forall m, Effects m fs -> effect m
}.

Instance Handles_hd {fs : list Effect}  {f : Effect} :
  Handles (f :: fs) f.
Proof.
  constructor; intros.
  inversion X.
  exact X0.
Defined.

Instance Handles_tl `{_ : Handles fs f} : Handles (x :: fs) f.
Proof.
  constructor; intros.
  inversion H.
  apply getEffect0.
  inversion X.
  exact X1.
Defined.

Axiom IO : Type -> Type.
Axiom IO_Functor : Functor IO.
Axiom IO_Applicative : Applicative IO.
Axiom IO_Monad : Monad IO.

Definition Kleisli m (A B : Type) := A -> m B.

Arguments Kleisli m A B.

Definition TFree `(xs : list Effect) a :=
  Kleisli IO (Effects IO xs) a.

Definition Eff := TFree.

Arguments Eff xs a.

Definition liftF `{Handles effects effect}
  `(getOp : effect IO -> IO a) : Eff effects a :=
  fun effects => getOp (getEffect IO effects).

Definition interpret `(interpreter : Effects IO effects)
  `(program : Eff effects a) : IO a := program interpreter.

Instance Impl_Functor {A} : Functor (fun B => A -> B) := {
  fmap := fun A B f run => fun xs => f (run xs)
}.

Instance Impl_Applicative {A} : Applicative (fun B => A -> B) := {
  pure := fun _ x => fun xs => x;
  ap   := fun A B runf runx => fun xs => runf xs (runx xs)
}.

Instance Impl_Monad {A} : Monad (fun B => A -> B) := {
  join := fun A run => fun xs => run xs xs
}.

Instance Kleisli_Functor `{Monad m} {A} : Functor (Kleisli m A) :=
  Compose_Functor.

Instance Kleisli_Applicative `{Applicative m} : Applicative (Kleisli m A) :=
  fun _ => @Compose_Applicative _ _ Impl_Applicative _.

Program Instance Kleisli_Monad_Distributes `{Monad m} {A} :
  @Monad_Distributes _ (@Impl_Monad A) m _ := {
  prod := _
}.
Obligation 1.
  exact (join (fmap (fun k => k X0) X)).
Defined.

(* Instance Kleisli_Monad `{Monad m} {A} : Monad (Kleisli m A) := Compose_Monad. *)

Instance TFree_Functor `(xs : list Effect) : Functor (TFree xs) := {
  fmap := fun A B f run => fun xs => fmap f (run xs)
}.

Instance TFree_Applicative `(xs : list Effect) : Applicative (TFree xs) := {
  pure := fun _ x => fun xs => pure x;
  ap   := fun A B runf runx => fun xs => runf xs <*> runx xs
}.

Instance TFree_Monad `(xs : list Effect) : Monad (TFree xs) := {
  join := fun A run => fun xs => run xs >>= fun f => f xs
}.

Record Abortive (m : Type -> Type) := {
  abortE : m unit
}.

Definition abort `{Handles r Abortive} : Eff r unit :=
  liftF abortE.

Record Reader (e : Type) (m : Type -> Type) := {
  askE : m e
}.

Definition ask `{Handles r (Reader e)} : Eff r e :=
  liftF (askE e).

Require Import Arith.

Set Printing Universes.

Definition example1 `{Handles r (Reader nat)} `{Handles r Abortive} :
  Eff r nat :=
  (fun x y => y + 15) <$> abort <*> ask.

Definition maybeInterpreter : Effects Maybe [Reader nat; Abortive] :=
  combine {| askE   := Just 10 |} (combine {| abortE := Nothing |} (NilE _)).

Definition run {a} : Eff [Reader nat; Abortive] a -> Maybe a :=
  interpret maybeInterpreter.

Example run_example1 : run example1 = Nothing.
Proof. reflexivity. Qed.

Definition example2 `{Handles r (Reader nat)} : Eff r nat :=
  fmap (plus 15) ask.

Example run_example2 : run example2 = Just 25.
Proof. reflexivity. Qed.

(*
Definition example3 `{Handles r (Reader nat)} `{Handles r Abortive} :
  Eff r nat :=
  v <- ask;
  if leb v 15
  then abort ;; pure 0
  else pure (v+1).

Example run_example3 : run example3 = None.
Proof. reflexivity. Qed.
*)