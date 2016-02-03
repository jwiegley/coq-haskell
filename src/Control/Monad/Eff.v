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

Definition TFree `(xs : list Effect) a :=
  forall `{Monad m}, Effects m xs -> m a.

Definition Eff := TFree.

Definition liftF `{Handles effects effect}
  `(getOp : forall m, effect m -> m a) : Eff effects a :=
  fun m H effects => getOp m (getEffect m effects).

Definition interpret `{H : Monad m} `(interpreter : Effects m effects)
  `(program : Eff effects a) : m a := program m H interpreter.

Instance TFree_Functor `(xs : list Effect) : Functor (TFree xs) := {
  fmap := fun A B f run => fun m H xs => fmap f (run m H xs)
}.

Instance TFree_Applicative `(xs : list Effect) : Applicative (TFree xs) := {
  pure := fun _ x => fun m H xs => pure x;
  ap   := fun A B runf runx => fun m H xs => runf m H xs <*> runx m H xs
}.

(* Instance TFree_Monad `(xs : list Effect) : Monad (TFree xs) := { *)
(*   join := fun A run => fun m H xs => run m H xs >>= fun f => f m H xs *)
(* }. *)

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