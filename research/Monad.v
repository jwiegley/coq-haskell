Require Export Applicative.
Require Import Coq.Lists.List.

Class Monad (M : Type -> Type) :=
{ is_applicative :> Applicative M

; join : forall {X}, M (M X) -> M X

; monad_law_1 : forall {X}, join ∘ fmap join = (@join X) ∘ join
; monad_law_2 : forall {X}, join ∘ fmap (@pure M is_applicative X) = id
; monad_law_3 : forall {X}, (@join X) ∘ pure = id
; monad_law_4 : forall {X Y} (f : X -> Y), join ∘ fmap (fmap f) = fmap f ∘ join
}.

Declare Scope Monad_scope.

Notation "join/ M" := (@join M _ _) (at level 28).
Notation "join/ M N" := (@join (fun X => M (N X)) _ _) (at level 26).

Definition bind {M} `{Monad M} {X Y}
  (f : (X -> M Y)) (x : M X) : M Y := join (fmap f x).

Notation "m >>= f" := (bind f m) (at level 25, left associativity).

(* Notation "x <- c1 ;; c2" := (@bind _ _ _ _ _ c1 (fun x => c2)) *)
(*   (at level 100, c1 at next level, right associativity). *)

Notation "X <- A ; B" := (A >>= (fun X => B))
  (right associativity, at level 84).

(* Notation "x : a <== c1 ;; c2" := (@bind _ _ _ _ _ c1 (fun x : a => c2)) *)
(*   (at level 100, c1 at next level, right associativity). *)

Notation "A ;; B" := (_ <- A ; B)
  (right associativity, at level 84).

Theorem monad_law_1_x
  : forall (M : Type -> Type) (m_dict : Monad M) A (x : M (M (M A))),
  join (fmap join x) = (@join M m_dict A) (join x).
Proof.
  intros.
  assert (join (fmap join x) = (join ∘ fmap join) x).
    unfold compose. reflexivity.
  assert (join (join x) = (join ∘ join) x).
    unfold compose. reflexivity.
  rewrite H. rewrite H0.
  rewrite monad_law_1.
  reflexivity.
Qed.

Theorem monad_law_2_x
  : forall (M : Type -> Type) (m_dict : Monad M) A (x : M A),
  join (fmap (@pure M _ A) x) = x.
Proof.
  intros.
  assert (join (fmap pure x) = (join ∘ fmap pure) x).
    unfold compose. reflexivity.
  rewrite H.
  rewrite monad_law_2.
  reflexivity.
Qed.

Theorem monad_law_3_x
  : forall (M : Type -> Type) (m_dict : Monad M) A (x : M A),
  (@join M m_dict A) (pure x) = x.
Proof.
  intros.
  assert (join (pure x) = (join ∘ pure) x).
    unfold compose. reflexivity.
  rewrite H.
  rewrite monad_law_3.
  reflexivity.
Qed.

Theorem monad_law_4_x
  : forall (M : Type -> Type) (m_dict : Monad M)
      A B (f : A -> B) (x : M (M A)),
  join (fmap (fmap f) x) = fmap f (join x).
Proof.
  intros.
  assert (join (fmap (fmap f) x) = (join ∘ fmap (fmap f)) x).
    unfold compose. reflexivity.
  assert (fmap f (join x) = (fmap f ∘ join) x).
    unfold compose. reflexivity.
  rewrite H. rewrite H0.
  rewrite monad_law_4.
  reflexivity.
Qed.

Theorem monad_assoc : forall `{M : Type -> Type} `{Monad M}
  {A B C} (m : M A) (f : A -> M B) (g : B -> M C),
  m >>= f >>= g = m >>= (fun x => f x >>= g).
Proof.
  intros.
  unfold bind.
  rewrite <- monad_law_4_x.
  rewrite fun_composition_x.
  rewrite <- monad_law_1_x.
  rewrite fun_composition_x.
  f_equal.
Qed.

#[export]
Program Instance option_Monad : Monad option := {
    join := fun _ x => match x with
      | None => None
      | Some None => None
      | Some (Some x) => Some x
      end
}.
Obligation 1.
  extensionality x.
  destruct x; auto;
  destruct o; auto;
  destruct o; auto.
Qed.
Obligation 2.
  extensionality x.
  destruct x; auto;
  destruct o; auto;
  destruct o; auto.
Qed.
Obligation 3.
  extensionality x.
  destruct x; auto;
  destruct o; auto;
  destruct o; auto.
Qed.
Obligation 4.
  extensionality x.
  destruct x; auto;
  destruct o; auto;
  destruct o; auto.
Qed.

Module Import LN := ListNotations.

#[export]
Program Instance list_Monad : Monad list := {
    join := @concat
}.
Obligation 1.
  extensionality l.
  induction l. crush.
  unfold compose in *. simpl.
  rewrite IHl.
Admitted.
Obligation 2.
  extensionality l.
  induction l. crush.
  unfold compose in *. simpl.
  rewrite IHl.
  unfold id. reflexivity.
Qed.
Obligation 3.
  extensionality l.
  induction l. crush.
  unfold compose, id in *.
  simpl. rewrite app_nil_r.
  reflexivity.
Qed.
Obligation 4.
  extensionality l.
  induction l. crush.
  unfold compose, id in *.
  simpl. rewrite IHl.
Admitted.
