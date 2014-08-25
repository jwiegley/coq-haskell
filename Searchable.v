Require Import Endo.
Require Import Applicative.
Require Import Monad.
Require Import HaskUtils.

Definition succ := S.

Inductive S (a : Type) :=
  | MkS : ((a -> bool) -> a) -> S a.

Arguments MkS [a] _.

Definition find {a} (xs : S a) : (a -> bool) -> a :=
  match xs with
    MkS f => f
  end.

Definition search {a} (xs : S a) (p : a -> bool) : option a :=
  let x := find xs p in if p x then Some x else None.

Definition forsome {a} (xs : S a) (p : a -> bool) : bool :=
  p (find xs p).

Definition forevery {a} (xs : S a) (p : a -> bool) : bool :=
  negb (forsome xs (fun x => negb (p x))).

Definition singleton {a} (x : a) : S a := MkS (fun p => x).

Definition doubleton {a} (x y : a) : S  a:=
  MkS (fun p => if p x then x else y).

Definition image {a b} (f : a -> b) (xs : S a) : S b :=
  MkS (fun q => f (find xs (fun x => q (f x)))).

Definition bigUnion {a} (xss : S (S a)) : S a :=
  MkS (fun p => find (find xss (fun xs => forsome xs p)) p).

Definition union {a} (xs ys : S a) : S a :=
  bigUnion (doubleton xs ys).

Program Instance S_Functor : Functor S := {
  fmap := fun _ _ => image
}.
Obligation 1.
  unfold image.
  extensionality xs.
  unfold id, find.
  destruct xs. f_equal.
Qed.

Definition S_apply {a b} (f : S (a -> b)) (xs : S a) : S b.
Proof.
  constructor.
  destruct xs. destruct f.
  intros. crush.
Defined.

Program Instance S_Applicative : Applicative S := {
  pure := fun _   => singleton;
  ap   := fun _ _ => S_apply
}.
Obligation 1.
  unfold S_apply.
  extensionality xs.
  destruct xs.
  unfold id. f_equal.
Qed.
Obligation 2.
  unfold S_apply.
  destruct u. destruct v. destruct w. crush.
Qed.
Obligation 5.
  unfold S_apply.
  extensionality xs.
  unfold image, singleton.
  destruct xs. crush.
Qed.

Program Instance S_Monad : Monad S := {
  join := fun _ => bigUnion
}.
Obligation 2. compute. extensionality x. destruct x. crush. Qed.
Obligation 3. compute. extensionality x. destruct x. crush. Qed.

Definition times {a b} : S a -> S b -> S (a * b) :=
  liftA2 S (fun x y => (x, y)).

Definition bit : S nat := doubleton O (succ O).

Fixpoint foldr {a b} (f : a -> b -> b) (z : b) (xs : list a) : b :=
  match xs with
    | nil => z
    | cons x xs' => foldr f (f x z) xs'
  end.

Definition sequence {a} {m : Type -> Type} `{Monad m}
  (ms : list (m a)) : m (list a) :=
  let k := liftA2 m (@cons a)
  in foldr k (pure nil) ms.

CoInductive stream (A : Type) : Type :=
  | Cons : A → stream A → stream A.

Arguments Cons [A] _ _.

CoFixpoint stream_map {A B} (f : A → B) (s : stream A) : stream B :=
  match s with
    | Cons x xs => Cons (f x) (stream_map f xs)
  end.

CoInductive stream_eq {a} : stream a -> stream a -> Prop :=
  | Stream_eq :
      forall h t1 t2, stream_eq t1 t2 -> stream_eq (Cons h t1) (Cons h t2).

Hypothesis stream_equality : forall {a} (x y : stream a),
  stream_eq x y -> x = y.

Definition sfrob {a} (s : stream a) : stream a :=
  match s with
    | Cons h t => Cons h t
  end.

Theorem sfrob_eq : forall {a} (s : stream a), s = sfrob s.
Proof. destruct s; reflexivity. Defined.

CoFixpoint repeated {a} (x : a) : stream a := Cons x (repeated x).

CoFixpoint unfoldr {a b} (f : b -> (a * b)) (z : b) : stream a :=
  match f z with
  | (a, b) => Cons a (unfoldr f b)
  end.

(* Sadly, we cannot define cantor over lazily infinite lists, nor can we use
   sequence on coinductive streams. *)
(* Definition cantor : S (stream nat) := sequence (repeated bit). *)
