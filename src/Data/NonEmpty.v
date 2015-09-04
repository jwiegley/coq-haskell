Require Import Hask.Prelude.

Require Import Coq.Sorting.Sorted.
Require Import Coq.Classes.RelationClasses.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** NonEmpty lists *)

Inductive NonEmpty (a : Type) : Type :=
  | NE_Sing : a -> NonEmpty a
  | NE_Cons : a -> NonEmpty a -> NonEmpty a.

Arguments NE_Sing [_] _.
Arguments NE_Cons [_] _ _.

Notation "[ ::: x1 ]" := (NE_Sing x1)
  (at level 0, format "[ :::  x1 ]") : seq_scope.

Fixpoint NE_from_list {a} (x : a) (xs : seq a) : NonEmpty a :=
  match xs with
    | nil => NE_Sing x
    | cons y ys => NE_Cons x (NE_from_list y ys)
  end.

Notation "[ ::: x & s ]" := (NE_from_list x s)
  (at level 0, only parsing) : seq_scope.

Fixpoint NE_length {a} (ne : NonEmpty a) : nat :=
  match ne with
    | NE_Sing x => 1
    | NE_Cons x xs => 1 + NE_length xs
  end.

Fixpoint NE_to_list {a} (ne : NonEmpty a) : list a :=
  match ne with
    | NE_Sing x => cons x nil
    | NE_Cons x xs => cons x (NE_to_list xs)
  end.

Coercion NE_to_list : NonEmpty >-> list.

Lemma NE_to_list_from_list {a} : forall (x : a) xs,
  NE_to_list (NE_from_list x xs) = x :: xs.
Proof.
  move=> x xs.
  elim: xs => //= [y ys IHys] in x *.
  by rewrite IHys.
Defined.

Definition NE_head {a} (ne : NonEmpty a) : a :=
  match ne with
    | NE_Sing x => x
    | NE_Cons x _ => x
  end.

Fixpoint NE_last {a} (ne : NonEmpty a) : a :=
  match ne with
    | NE_Sing x => x
    | NE_Cons x xs => NE_last xs
  end.

Fixpoint NE_belast a (ne : NonEmpty a) : seq a :=
  match ne with
    | NE_Sing x => [::]
    | NE_Cons x xs => x :: NE_belast xs
  end.

Fixpoint NE_rcons {a} (ne : NonEmpty a) z :=
  match ne with
    | NE_Sing x => NE_Cons x (NE_Sing z)
    | NE_Cons x xs => NE_Cons x (NE_rcons xs z)
  end.

CoInductive NE_last_spec {a} : NonEmpty a -> Type :=
  | NE_LastSing x     : NE_last_spec [::: x]
  | NE_LastRcons s x  : NE_last_spec (NE_rcons s x).

Lemma NE_lastI a (x : a) s :
  NE_Cons x s = NE_rcons (NE_from_list x (NE_belast s)) (NE_last s).
Proof.
  elim: s => //= [y ys IHys] in x *.
  by rewrite IHys.
Qed.

Lemma NE_lastP a s : @NE_last_spec a s.
Proof. case: s => [|x s]; [left | rewrite NE_lastI; right]. Qed.

Lemma NE_Cons_spec a (x : a) xs : NE_Cons x xs = NE_from_list x (NE_to_list xs).
Proof.
  by elim: xs => //= [y ys IHys] in x *; congr (NE_Cons _ _).
Qed.

Lemma ne_list : forall a (x : a) xs ns,
  NE_to_list ns = x :: xs -> ns = NE_from_list x xs.
Proof.
  move=> a x xs ns H.
  replace ns with (NE_from_list x xs); last first.
    case: ns => [r|r rs] in H *.
      by inversion H.
    by inversion H; rewrite NE_Cons_spec.
  by [].
Defined.

Lemma NE_head_from_list a (x : a) xs :
  NE_head (NE_from_list x xs) = head x (x :: xs).
Proof. by elim E: xs => // [*] in x *. Qed.

Lemma NE_last_from_list a (x : a) xs : NE_last (NE_from_list x xs) = last x xs.
Proof. by elim: xs => //= [*] in x *. Qed.

Fixpoint NE_map {a b : Type} (f : a -> b) (ne : NonEmpty a) : NonEmpty b :=
  match ne with
    | NE_Sing x => NE_Sing (f x)
    | NE_Cons x xs => NE_Cons (f x) (NE_map f xs)
  end.

Definition NE_foldl {a b : Type} (f : a -> b -> a) (z : a)
  (ne : NonEmpty b) : a := foldl f z ne.
Arguments NE_foldl {a b} f z ne /.

Definition NE_foldr {a b : Type} (f : b -> a -> a) (z : a)
  (ne : NonEmpty b) : a := foldr f z ne.
Arguments NE_foldr {a b} f z ne /.

Fixpoint NE_mapAccumL {A X Y : Type} (f : A -> X -> (A * Y))
  (s : A) (v : NonEmpty X) : A * NonEmpty Y :=
  match v with
  | NE_Sing x =>
    let: (s', y) := f s x in
    (s', NE_Sing y)
  | NE_Cons x xs =>
    let: (s', y) := f s x in
    let: (s'', ys) := NE_mapAccumL f s' xs in
    (s'', NE_Cons y ys)
  end.

Fixpoint NE_append {a : Type} (l1 l2 : NonEmpty a) : NonEmpty a :=
  match l1 with
    | NE_Sing x => NE_Cons x l2
    | NE_Cons x xs => NE_Cons x (NE_append xs l2)
  end.

Lemma NE_head_append_spec : forall {a} {xs ys : NonEmpty a},
  NE_head (NE_append xs ys) = NE_head xs.
Proof. induction xs; auto. Qed.

Lemma NE_last_append_spec : forall {a} {xs ys : NonEmpty a},
  NE_last (NE_append xs ys) = NE_last ys.
Proof. induction xs; auto. Qed.

Lemma NE_append_from_list : forall {a} (x : a) xs y ys,
  NE_from_list x (xs ++ y :: ys) =
  NE_append (NE_from_list x xs) (NE_from_list y ys).
Proof.
  move=> a x xs y ys.
  elim: xs => //= [z zs IHzs] in x y ys *.
  f_equal.
  exact: IHzs.
Defined.

(*
Definition NE_last_ind P a :
  (forall (x : a), P a [::: x])
    -> (forall s x, P a s -> P a (NE_rcons s x))
    -> forall s, P a s.
Proof.
  move=> Hsing Hlast s.
  elim: s => [x|x s2 IHs2].
    exact: Hsing.
  replace (NE_Cons x s2) with (NE_append [::: x] s2); last by [].
  set s := [::: x].
  elim: s2 => [x2|x2 s3 IHs3] in IHs2 *.
    replace (NE_append s [::: x2])
      with (NE_rcons s x2); last by [].
    exact: (Hlast s x2 (Hsing _)).
  replace (NE_append s (NE_Cons x2 s3))
    with (NE_append (NE_rcons [::: x] x2) s3); last by [].
*)

Section Sorted.

Variable A : Set.
Variable R : A -> A -> Prop.
Context `{H : Transitive A R}.

Inductive NE_Forall (P : A -> Prop) : NonEmpty A -> Prop :=
 | NE_Forall_sing : forall x, P x -> NE_Forall P (NE_Sing x)
 | NE_Forall_cons : forall x l, P x -> NE_Forall P l
                      -> NE_Forall P (NE_Cons x l).

Hint Constructors NE_Forall.

Definition NE_all_true  (f : A -> bool) := NE_Forall (fun x => f x = true).
Definition NE_all_false (f : A -> bool) := NE_Forall (fun x => f x = false).

Lemma NE_Forall_head : forall P (xs : NonEmpty A),
  NE_Forall P xs -> P (NE_head xs).
Proof. induction xs; intros; inversion H0; assumption. Qed.

Lemma NE_Forall_last : forall P (xs : NonEmpty A),
  NE_Forall P xs -> P (NE_last xs).
Proof.
  intros. induction xs; simpl in *.
    inversion H0. assumption.
  apply IHxs. inversion H0. assumption.
Qed.

Section Membership.

Fixpoint NE_member (z : A) (ne : NonEmpty A) : Prop :=
  match ne with
    | NE_Sing x => x = z
    | NE_Cons x xs => (x = z) \/ NE_member z xs
  end.

Lemma NE_Forall_member_spec (z : A) (ne : NonEmpty A) :
  forall f, NE_Forall f ne -> NE_member z ne -> f z.
Proof.
  induction ne; simpl; intros.
    inversion H0. subst. assumption.
  inversion H1.
    inversion H0. subst. assumption.
  apply IHne.
    inversion H0. assumption.
  assumption.
Qed.

End Membership.

Inductive NE_StronglySorted : NonEmpty A -> Prop :=
  | NE_SSorted_sing a   : NE_StronglySorted (NE_Sing a)
  | NE_SSorted_cons a l : NE_StronglySorted l -> NE_Forall (R a) l
                            -> NE_StronglySorted (NE_Cons a l).

Lemma NE_StronglySorted_to_list : forall xs,
  NE_StronglySorted xs -> StronglySorted R (NE_to_list xs).
Proof.
  elim=> [x|x xs IHxs] /=.
    by constructor; constructor.
  move=> Hsort.
  constructor.
    apply: IHxs.
    by inversion Hsort.
  case: xs => [y|y ys] in IHxs Hsort *.
    constructor.
      inversion Hsort; subst.
      by inversion H3.
    by constructor.
  constructor.
    inversion Hsort; subst.
    by inversion H3.
  inversion Hsort; subst.
  specialize (IHxs H2).
  inversion IHxs.
  rewrite -/NE_to_list.
  inversion H3; subst.
  have: forall a, R y a -> R x a.
    move=> a Ha.
    exact: transitivity H8 Ha.
  move/List.Forall_impl.
  exact.
Qed.

End Sorted.

Arguments NE_all_true  [A] f _.
Arguments NE_all_false [A] f _.

Module NonEmptyNotations.

Notation " [ x ] " := (NE_Sing x) : list_scope.
Notation " [ x ; y ] " := (NE_Cons x (NE_Sing y)) : list_scope.
Notation " [ x ; y ; z ] " := (NE_Cons x (NE_Cons y (NE_Sing z))) : list_scope.
Notation " [ x ; y ; z ; w ] " :=
  (NE_Cons x (NE_Cons y (NE_Cons z (NE_Sing w)))) : list_scope.
Notation " [ x ; y ; z ; w ; v ] " :=
  (NE_Cons x (NE_Cons y (NE_Cons z (NE_Cons w (NE_Sing v))))) : list_scope.

Infix "++" := NE_append.

End NonEmptyNotations.
