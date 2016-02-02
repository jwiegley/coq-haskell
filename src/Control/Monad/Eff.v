Require Import
  Hask.Control.Monad
  Hask.Control.Monad.Free
  Coq.Lists.List.

Generalizable All Variables.

Import ListNotations.

Definition Effects := list (Type -> Type).

Fixpoint nth_maybe {A} (n : nat) (l : list A) : option A :=
  match n with
  | 0   => match l with [] => None | x :: _ => Some x end
  | S m => match l with [] => None | _ :: t => nth_maybe m t end
  end.

Lemma nth_maybe_empty : forall A n, nth_maybe n [] = @None A.
Proof. intros; destruct n; auto. Qed.

Class Handles (f : Type -> Type) `(r : Effects) := {
  handles_index  : nat;
  handles_effect : nth_maybe handles_index r = Some f
}.

Arguments Handles f r.

Program Instance Handles_hd `(fs : Effects) : Handles f (f :: fs).
Obligation 1. apply 0. Defined.

Program Instance Handles_tl `(_ : Handles f fs) : Handles f (x :: fs).
Obligation 1. apply (S handles_index). Defined.
Obligation 2. apply handles_effect. Defined.

Definition Handles_inv_cons f g `(gs : Effects)
  (H : Handles f (g :: gs)) : (f = g) + Handles f gs.
Proof.
  destruct H.
  destruct handles_index0.
    left.
    inversion handles_effect0.
    reflexivity.
  right.
  econstructor.
  apply handles_effect0.
Defined.

Inductive Union (r : Effects) (a : Type) :=
  Inj : forall `{Functor f} `{Handles f r}, f a -> Union r a.

Arguments Inj {r a f _ _} _.

Instance Union_Functor `(r : Effects) : Functor (Union r) := {
  fmap := fun _ _ f x => match x with Inj _ _ _ x => Inj (fmap f x) end
}.

Lemma Union_empty_contra : forall x, Union [] x -> False.
Proof.
  intros.
  inversion X.
  inversion H0.
  rewrite nth_maybe_empty in handles_effect0.
  discriminate.
Qed.

Program Definition Union_inv_sing `(u : Union [f] a) : f a :=
  match u with Inj f F H v => _ end.
Obligation 1.
  inversion H.
  destruct handles_index0.
    inversion handles_effect0.
    assumption.
  simpl in handles_effect0.
  rewrite nth_maybe_empty in handles_effect0.
  discriminate.
Defined.

Inductive sum' (A B : Type) : Type :=
  | inl' : A -> sum' A B
  | inr' : B -> sum' A B.

Definition Union_inv_cons `(fs : Effects)
  `(u : Union (f :: fs) a) : sum' (f a) (Union fs a).
Proof.
  destruct u.
  apply Handles_inv_cons in H0.
  inversion H0.
    subst; left.
    assumption.
  right.
  econstructor.
  apply H.
  apply H1.
  apply f1.
Defined.

Definition Eff `(r : Effects) := Free (Union r).

(*
Definition univ_check `{r : Effects} : Free (Union r) (Free (Union r) nat) :=
  pure[Free (Union r)] (pure[Free (Union r)] 10).
*)

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