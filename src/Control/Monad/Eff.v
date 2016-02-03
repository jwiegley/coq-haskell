Require Import
  Hask.Control.Monad
  Coq.Lists.List.

Generalizable All Variables.

Import ListNotations.

Definition Effect := (Type -> Type) -> Type.

Inductive Effects (m : Type -> Type) : list Effect -> Type :=
  | EmptyE : Effects m []
  | ConsE effects : forall effect : Effect,
      effect m -> Effects m effects -> Effects m (effect :: effects).

Arguments ConsE : default implicits.

Infix ".:" := ConsE (at level 100).

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

Instance TFree_Monad `(xs : list Effect) : Monad (TFree xs) := {
  join := fun A run => fun m H xs => run m H xs >>= fun f => f m H xs
}.

Definition runPure `(c : Eff [] a) : a :=
  match c with
  | Pure x => x
  | Join x k f => False_rect _ (Union_empty_contra _ f)
  end.

Inductive Exec (e : Type -> Type) `(r : Effects) (a b : Type) :=
  | Value  : a -> Exec e r a b
  | Action : forall x, (x -> Eff r b) -> e x -> Exec e r a b.

Arguments Value {e r a b} _.
Arguments Action {e r a b x} _ _.

Definition Handler e `(r : Effects) a b := Exec e r a b -> Eff r b.

Fixpoint handle `{r : Effects} `(h : Handler e r a b)
  (x : Eff (e :: r) a) : Eff r b :=
  match x with
  | Pure v => h (Value v)
  | Join _ k u =>
    match Union_inv_cons r u with
    | inl' v => h (Action (handle h \o k) v)
    | inr' u' => Join (handle h \o k) u'
    end
  end.

Inductive Abortive (a : Type) :=
  | Exit : a -> Abortive a.

Instance Abortive_Functor : Functor Abortive := {
  fmap := fun _ _ f x => match x with Exit e => Exit _ (f e) end
}.

Definition abort `{Handles Abortive r} : Eff r unit :=
  Join Pure (Inj (Exit _ tt)).

Fixpoint abortHandler `{r : Effects} {a} : Handler Abortive r a (option a) :=
  fun c : Exec Abortive r a (option a) =>
    match c with
    | Value v => Pure (Some v)
    | Action _ _ (Exit _) => Pure None
    end.

Inductive Reader (e : Type) (a : Type) :=
  | Ask : (e -> a) -> Reader e a.

Instance Reader_Functor (e : Type) : Functor (Reader e) := {
  fmap := fun _ _ f x => match x with Ask k => Ask _ _ (f \o k) end
}.

Definition ask `{Handles (Reader e) r} : Eff r e :=
  Join Pure (Inj (Ask _ _ id)).

Fixpoint readerHandler `{r : Effects} {e a} (x : e) :
  Handler (Reader e) r a a := fun c =>
    match c with
    | Value v => Pure v
    | Action _ k (Ask f) => k (f x)
    end.

Require Import Arith.

Set Printing Universes.

Definition example1 `{Handles (Reader nat) r} `{Handles Abortive r} :
  Eff r nat :=
  (fun x y => y + 15) <$> abort <*> ask.

Definition run {a} : Eff [Reader nat; Abortive] a -> option a :=
  runPure \o handle abortHandler \o handle (readerHandler 10).

Example run_example1 : run example1 = None.
Proof. reflexivity. Qed.

Definition example2 `{Handles (Reader nat) r} : Eff r nat :=
  fmap (plus 15) ask.

Example run_example2 : run example2 = Some 25.
Proof. reflexivity. Qed.

(*
Definition example3 `{Handles (Reader nat) r} `{Handles Abortive r} :
  Eff r nat :=
  v <- ask;
  if leb v 15
  then abort ;; pure 0
  else pure (v+1).

Example run_example3 : run example3 = None.
Proof. reflexivity. Qed.
*)