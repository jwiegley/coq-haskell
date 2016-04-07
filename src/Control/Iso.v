Require Import Hask.Ltac.
Require Import Hask.Prelude.
Require Import Hask.Control.Applicative.
Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.Cont.
Require Import Hask.Control.Monad.State.
Require Import Hask.Data.Functor.Contravariant.
Require Import Hask.Data.Functor.Identity.
Require Import Hask.Data.Functor.Kan.
Require Import Hask.Data.Functor.Yoneda.
Require Import Hask.Control.Lens.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Init.Datatypes.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** Type Constants *)

Definition zero := False.
Definition one  := unit.
Definition two  := bool.

(** Tactic helpers *)

Require Import FunctionalExtensionality.

Ltac extensionalize A B C :=
  intuition;
  unfold comp, id; simpl;
  try extensionality A;
  try extensionality B;
  try extensionality C;
  try destruct A;
  try destruct B;
  try destruct C;
  simpl in *;
  repeat (match goal with
          | [ H : zero     |- _ ] => contradiction H
          | [ H : False    |- _ ] => contradiction H
          | [ H : one      |- _ ] => destruct H
          | [ H : unit     |- _ ] => destruct H
          | [ H : two      |- _ ] => destruct H
          | [ H : bool     |- _ ] => destruct H
          | [ H : sum _ _  |- _ ] => destruct H
          | [ H : prod _ _ |- _ ] => destruct H
          end);
  auto.

(** Isomorphisms *)

Infix "∘" := comp (at level 50).

Definition isomorphic (X Y : Type) : Prop :=
  exists (f : X -> Y) (g : Y -> X), f ∘ g = id /\ g ∘ f = id.

Notation "X ≅ Y" := (isomorphic X Y) (at level 100).

Axiom iso_ext : forall {A : Type} (f g : A -> Type),
  (forall x, f x ≅ g x) -> ((forall x, f x) ≅ (forall x, g x)).

Program Instance Iso_Equivalence : Equivalence isomorphic.
Obligation 1.
  intro x.
  do 2 exists id.
  firstorder.
Qed.
Obligation 2.
  firstorder.
Qed.
Obligation 3.
  intros x y z H1 H2.
  firstorder.
  exists (x1 ∘ x0).
  exists (x2 ∘ x3).
  rewrite comp_assoc.
  assert ((x1 ∘ x0) ∘ x2 = x1 ∘ (x0 ∘ x2))
    by (rewrite comp_assoc; trivial).
  assert ((x2 ∘ x3) ∘ x1 = x2 ∘ (x3 ∘ x1))
    by (rewrite comp_assoc; trivial).
  split.
    rewrite H3, H, <- H0; trivial.
  rewrite comp_assoc, H4, H2, <- H1; trivial.
Qed.

Add Parametric Relation {A B : Type} : Type isomorphic
  reflexivity proved by (@Equivalence_Reflexive _ _ Iso_Equivalence)
  symmetry proved by (@Equivalence_Symmetric _ _ Iso_Equivalence)
  transitivity proved by (@Equivalence_Transitive _ _ Iso_Equivalence)
  as isomorphic_relation.

Add Parametric Morphism : Basics.arrow
  with signature (isomorphic ==> isomorphic ==> isomorphic)
    as fun_isomorphism.
(* function types respect isomorphism *)
Proof.
  intros.
  destruct H as [from_x].
  destruct H as [to_x].
  destruct H0 as [from_x0].
  destruct H0 as [to_x0].
  unfold isomorphic.
  exists (fun k y => from_x0 (k (to_x y))).
  exists (fun k x => to_x0 (k (from_x x))).
  extensionalize A B C.
  - replace (from_x (to_x B)) with ((from_x ∘ to_x) B); trivial.
    rewrite H1.
    unfold id.
    replace (from_x0 (to_x0 (A B))) with ((from_x0 ∘ to_x0) (A B)); trivial.
    rewrite H.
    reflexivity.
  - replace (to_x (from_x B)) with ((to_x ∘ from_x) B); trivial.
    rewrite H2.
    unfold id.
    replace (to_x0 (from_x0 (A B))) with ((to_x0 ∘ from_x0) (A B)); trivial.
    rewrite H3.
    reflexivity.
Qed.

Add Parametric Morphism : isomorphic
  with signature (isomorphic --> isomorphic ++> Basics.impl)
    as impl_isomorphism.
(* implication respects isomorphism *)
Proof.
  intros.
  rewrite H, <- H0.
  reflexivity.
Qed.

Add Parametric Morphism : isomorphic
  with signature (isomorphic --> isomorphic ++> Basics.flip Basics.impl)
    as flip_impl_isomorphism.
(* flipped implication respects isomorphism *)
Proof.
  intros.
  rewrite H, <- H0.
  reflexivity.
Qed.

Class Isomorphism (X Y : Type) := {
  to       : X -> Y;
  from     : Y -> X;
  iso_to   : to ∘ from = id;
  iso_from : from ∘ to = id
}.

Theorem Isomorphism_is_iso : forall `{Isomorphism A B}, (A ≅ B).
Proof.
  intros.
  destruct H.
  exists to0.
  exists from0.
  auto.
Qed.

(** Adjoint Functors *)

Definition adjoint (f g : Type -> Type) : Prop :=
  forall a b, f a -> b ≅ a -> g b.

Notation "F ⊣ G" := (adjoint F G) (at level 100).

Theorem curry_adj : forall a, (fun b => a * b)%type ⊣ (fun b => a -> b).
Proof.
  intros.
  unfold adjoint; intros.
  exists (fun k a b => k (b, a)).
  exists (fun k p => k (snd p) (fst p)).
  extensionalize A B C.
Qed.
Arguments curry_adj {a _ _} /.

(** Representable Functors *)

Definition representable (f : Type -> Type) : Prop :=
  forall a, exists R, R -> a ≅ f a.

(** Sums (coproducts, type addition) *)

Lemma f_comp {A B C} (f : B -> C) (g : A -> B) (z : A) :
  f (g z) = (f ∘ g) z.
Proof. reflexivity. Qed.

Add Parametric Morphism : sum
  with signature (isomorphic ==> isomorphic ==> isomorphic)
    as sum_isomorphism.
(* coproducts respect isomorphism *)
Proof.
  intros.
  destruct H as [from_x].
  destruct H as [to_x].
  destruct H0 as [from_x0].
  destruct H0 as [to_x0].
  exists (fun p => match p with
                   | inl x  => inl (from_x x)
                   | inr x0 => inr (from_x0 x0)
                   end).
  exists (fun p => match p with
                   | inl y  => inl (to_x y)
                   | inr y0 => inr (to_x0 y0)
                   end).
  extensionalize A B C;
  [ rewrite (f_comp from_x), H1
  | rewrite (f_comp from_x0), H
  | rewrite (f_comp to_x), H2
  | rewrite (f_comp to_x0), H3 ]; trivial.
Qed.

Theorem add_zero_iso : forall a, a + zero ≅ a.
Proof.
  intros.
  exists (fun p => match p with
                   | inl x => x
                   | inr f => False_rect _ f
                   end).
  exists (fun a => inl a).
  extensionalize A B C.
Qed.
Hint Rewrite add_zero_iso : isos.

Theorem zero_add_iso : forall a, zero + a ≅ a.
Proof.
  intros.
  exists (fun p => match p with
                   | inl f => False_rect _ f
                   | inr x => x
                   end).
  exists (fun a => inr a).
  extensionalize A B C.
Qed.
Hint Rewrite zero_add_iso : isos.

Theorem add_assoc_iso : forall a b c, (a + b) + c ≅ a + (b + c).
Proof.
  intros.
  exists (fun p => match p with
                   | inl (inl x) => inl x
                   | inl (inr x) => inr (inl x)
                   | inr x       => inr (inr x)
                   end).
  exists (fun p => match p with
                   | inl x       => inl (inl x)
                   | inr (inl x) => inl (inr x)
                   | inr (inr x) => inr x
                   end).
  extensionalize A B C.
Qed.

Theorem add_sym_iso : forall a b, a + b ≅ b + a.
Proof.
  intros.
  exists (fun p => match p with
                   | inl x => inr x
                   | inr x => inl x
                   end).
  exists (fun p => match p with
                   | inl x => inr x
                   | inr x => inl x
                   end).
  extensionalize A B C.
Qed.

(** Products (type multiplication) *)

Add Parametric Morphism : prod
  with signature (isomorphic ==> isomorphic ==> isomorphic)
    as prod_isomorphism.
(* products respect isomorphism *)
Proof.
  intros.
  destruct H as [from_x].
  destruct H as [to_x].
  destruct H0 as [from_x0].
  destruct H0 as [to_x0].
  exists (fun p => match p with
                     (x, x0)  => (from_x x, from_x0 x0)
                   end).
  exists (fun p => match p with
                     (y, y0)  => (to_x y, to_x0 y0)
                   end).
  extensionalize A B C;
  [ rewrite (f_comp from_x), H1;
    rewrite (f_comp from_x0), H
  | rewrite (f_comp to_x), H2;
    rewrite (f_comp to_x0), H3 ]; trivial.
Qed.

Theorem mul_zero_iso : forall a, a * zero ≅ zero.
Proof.
  intros.
  exists (fun p => snd p).
  exists (fun f => False_rect _ f).
  extensionalize A B C.
Qed.
Hint Rewrite mul_zero_iso : isos.

Theorem zero_mul_iso : forall a, zero * a ≅ zero.
Proof.
  intros.
  exists (fun p => fst p).
  exists (fun f => False_rect _ f).
  extensionalize A B C.
Qed.
Hint Rewrite zero_mul_iso : isos.

Theorem mul_one_iso : forall a, a * one ≅ a.
Proof.
  intros;
  exists (fun p => fst p);
  exists (fun a => (a, tt));
  extensionalize A B C.
Qed.
Hint Rewrite mul_one_iso : isos.

Theorem one_mul_iso : forall a, one * a ≅ a.
Proof.
  intros;
  exists (fun p => snd p);
  exists (fun a => (tt, a));
  extensionalize A B C.
Qed.
Hint Rewrite one_mul_iso : isos.

Theorem mul_two_iso : forall a, a * two ≅ a + a.
Proof.
  intros.
  exists (fun (p : a * bool) => if snd p then inl (fst p) else inr (fst p)).
  exists (fun p => match p with
                   | inl x => (x, true)
                   | inr x => (x, false)
                   end).
  extensionalize A B C.
Qed.
Hint Rewrite mul_two_iso : isos.

Theorem two_mul_iso : forall a, two * a ≅ a + a.
Proof.
  intros;
  exists (fun (p : bool * a) => if fst p then inl (snd p) else inr (snd p)).
  exists (fun p => match p with
                   | inl x => (true, x)
                   | inr x => (false, x)
                   end).
  extensionalize A B C.
Qed.
Hint Rewrite two_mul_iso : isos.

Theorem mul_assoc_iso : forall a b c, (a * b) * c ≅ a * (b * c).
Proof.
  intros;
  exists (fun p => match p with ((a, b), c) => (a, (b, c)) end);
  exists (fun p => match p with (a, (b, c)) => ((a, b), c) end).
  extensionalize A B C.
Qed.

Theorem mul_sym_iso : forall a b, a * b ≅ b * a.
Proof.
  intros;
  exists (fun p => match p with (a, b) => (b, a) end);
  exists (fun p => match p with (b, a) => (a, b) end).
  extensionalize A B C.
Qed.

(** Addition distributes over multiplication *)

Theorem mul_add_iso : forall a b c, a * (b + c) ≅ (a * b) + (a * c).
Proof.
  intros.
  exists (fun p => match p with
                   | (a, inl b) => inl (a, b)
                   | (a, inr c) => inr (a, c)
                   end).
  exists (fun p => match p with
                   | inl (a, b) => (a, inl b)
                   | inr (a, c) => (a, inr c)
                   end).
  extensionalize A B C.
Qed.
Hint Rewrite mul_add_iso : isos.

Theorem add_mul_iso : forall a b c, (a + b) * c ≅ (a * c) + (b * c).
Proof.
  intros.
  exists (fun p => match p with
                   | (inl a, c) => inl (a, c)
                   | (inr b, c) => inr (b, c)
                   end).
  exists (fun p => match p with
                   | inl (a, c) => (inl a, c)
                   | inr (b, c) => (inr b, c)
                   end).
  extensionalize A B C.
Qed.
Hint Rewrite add_mul_iso : isos.

Theorem add_mul_add_iso : forall a b c,
  (a + b) * (a + c) ≅ (a * a) + (a * c) + (b * a) + (b * c).
Proof.
  intros.
  exists (fun p => match p with
                   | (inl x, inl y) => inl (inl (inl (x, y)))
                   | (inl x, inr y) => inl (inl (inr (x, y)))
                   | (inr x, inl y) => inl (inr (x, y))
                   | (inr x, inr y) => inr (x, y)
                   end).
  exists (fun p => match p with
                   | inl (inl (inl (x, y))) => (inl x, inl y)
                   | inl (inl (inr (x, y))) => (inl x, inr y)
                   | inl (inr (x, y))       => (inr x, inl y)
                   | inr (x, y)             => (inr x, inr y)
                   end).
  extensionalize A B C.
Qed.
Hint Rewrite add_mul_add_iso : isos.

Theorem add_one_mul_iso : forall a b, (a + one) * b ≅ (a * b) + b.
Proof.
  intros.
  exists (fun p => match p with
                   | (inl a, b)  => inl (a, b)
                   | (inr tt, b) => inr b
                   end).
  exists (fun p => match p with
                   | inl (a, b) => (inl a, b)
                   | inr b      => (inr tt, b)
                   end).
  extensionalize A B C.
Qed.
Hint Rewrite add_one_mul_iso : isos.

(** Exponentials (type exponentiation) *)

Theorem exp_zero_iso : forall a, zero -> a ≅ one.
(* a^0 = 1 *)
Proof.
  intros.
  exists (fun _ => tt).
  exists (fun _ f => False_rect _ f).
  extensionalize A B C.
Qed.
Hint Rewrite exp_zero_iso : isos.

Theorem exp_one_iso : forall a, one -> a ≅ a.
(* a^1 = a *)
Proof.
  intros.
  exists (fun k => k tt).
  exists (fun a _ => a).
  extensionalize A B C.
Qed.
Hint Rewrite exp_one_iso : isos.

Theorem one_exp_iso : forall a, a -> one ≅ one.
(* 1^a = a *)
Proof.
  intros.
  exists (fun _ => tt).
  exists (fun u _ => u).
  extensionalize A B C.
Qed.
Hint Rewrite one_exp_iso : isos.

Theorem exp_two_iso : forall a, two -> a ≅ a * a.
Proof.
  intros.
  exists (fun k => (k true, k false)).
  exists (fun p (b : bool) => if b then fst p else snd p).
  extensionalize A B C.
Qed.
Hint Rewrite exp_two_iso : isos.

Theorem exp_exp_sym_iso : forall a b c, b -> a -> c ≅ a -> b -> c.
(* (c^a)^b = (c^b)^a *)
Proof. intros; do 2 exists Basics.flip; intuition. Qed.

Lemma exp_exp_sym_dep_iso : forall (a c : Type) (d : c -> Type),
  (a -> forall b : c, d b) ≅ (forall b : c, a -> d b).
Proof.
  intuition.
  unfold isomorphic.
  exists (fun f b a => f a b).
  exists (fun f a b => f b a).
  extensionalize A B C.
Qed.

(** Exponentiation and multiplication distribute *)

Theorem exp_add_iso : forall a b c,
  ((a + b) -> c) -> c ≅ (a -> c) -> (b -> c) -> c.
Proof.
  intros.
  exists (fun k l r => k (fun p => match p with
                                   | inl x => l x
                                   | inr x => r x
                                   end)).
  exists (fun k p => k (fun a => p (inl a)) (fun a => p (inr a))).
  extensionalize A B C.
  f_equal.
  extensionality p.
  destruct p; trivial.
Qed.
Hint Rewrite exp_add_iso : isos.

Theorem mul_exp_iso : forall a b c, a -> (b * c) ≅ (a -> b) * (a -> c).
(* (b * c)^a = b^a * c^a *)
Proof.
  intros;
  exists (fun k => ((fun a => fst (k a)), (fun a => snd (k a)))).
  exists (fun p a => match p with (f, g) => (f a, g a) end).
  extensionalize A B C.
Qed.
Hint Rewrite mul_exp_iso : isos.

Corollary exp_mul_iso : forall a b c, (a * b) -> c ≅ a -> b -> c.
(* c^(a * b) = (c^b)^a *)
Proof. intros; rewrite curry_adj, exp_exp_sym_iso; reflexivity. Qed.
Hint Rewrite exp_mul_iso : isos.

Lemma exp_ex_iso : forall A (P : A -> Prop) (r : Prop),
  (exists x : A, P x) -> r ≅ (forall x : A, P x -> r).
Proof.
  intros.
  exists (fun p x H => p (ex_intro _ x H)).
  exists (fun (k : forall x : A, P x -> r) p =>
            match p with ex_intro x H => k x H end).
  extensionalize A B C.
Qed.
Hint Rewrite exp_ex_iso : isos.

Lemma exp_sig_iso : forall A (P : A -> Prop) r,
  { x : A | P x } -> r ≅ (forall x : A, P x -> r).
Proof.
  intros.
  exists (fun p x H => p (exist _ x H)).
  exists (fun k p => match p with exist x H => k x H end).
  extensionalize A B C.
Qed.
Hint Rewrite exp_sig_iso : isos.

Lemma exp_sigT_iso : forall A (P : A -> Type) r,
  { x : A & P x } -> r ≅ (forall x : A, P x -> r).
Proof.
  intros.
  exists (fun p x H => p (existT _ x H)).
  exists (fun k p => match p with existT x H => k x H end).
  extensionalize A B C.
Qed.
Hint Rewrite exp_sigT_iso : isos.

Corollary exp_add_more_iso : forall a b c d,
  (d -> (a + b) -> c) -> c ≅ (d -> a -> c) -> (d -> b -> c) -> c.
Proof.
  intros.
  rewrite <- exp_mul_iso, mul_add_iso, exp_add_iso, !exp_mul_iso.
  reflexivity.
Qed.

Lemma f_exp_iso : forall a b c, (b ≅ c) -> (a -> b ≅ a -> c).
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma f_exp_dep_iso : forall a b c,
  (b ≅ c) -> ((forall x : a, b) ≅ (forall x : a, c)).
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

(** Multiplication by a constant *)

Fixpoint mul (n : nat) (a : Type) : Type :=
  match n with
  | O    => zero
  | S O  => a
  | S n' => (a + mul n' a)%type
  end.

Example mul_zero : forall a, mul 0 a = zero.
Proof. reflexivity. Qed.
Example mul_one : forall a, mul 1 a = a.
Proof. reflexivity. Qed.
Example mul_two : forall a, mul 2 a = (a + a)%type.
Proof. reflexivity. Qed.
Example mul_three : forall a, mul 3 a = (a + (a + a))%type.
Proof. reflexivity. Qed.

Lemma mul_S_iso : forall a n, mul (S n) a ≅ a + mul n a.
Proof.
  induction n;
  rewrite ?add_zero_iso;
  reflexivity.
Qed.
Hint Rewrite mul_S_iso : isos.

Add Parametric Morphism : mul
  with signature (eq ==> isomorphic ==> isomorphic)
    as mul_isomorphism.
Proof.
  intros n a t H.
  induction n.
    reflexivity.
  rewrite !mul_S_iso, IHn, H.
  reflexivity.
Qed.

Hint Rewrite plus_Sn_m : isos.

Theorem mul_plus_iso : forall a n m, mul (n + m) a ≅ mul n a + mul m a.
Proof.
  induction n; intros.
    rewrite zero_add_iso.
    reflexivity.
  autorewrite with isos.
  rewrite IHn, add_assoc_iso.
  reflexivity.
Qed.
Hint Rewrite mul_plus_iso : isos.

(** Exponentation by a constant *)

Fixpoint exp (n : nat) (a : Type) : Type :=
  match n with
  | O    => one
  | S O  => a
  | S n' => (a * exp n' a)%type
  end.

Example exp_zero : forall a, exp 0 a = one.
Proof. reflexivity. Qed.
Example exp_one : forall a, exp 1 a = a.
Proof. reflexivity. Qed.
Example exp_two : forall a, exp 2 a = (a * a)%type.
Proof. reflexivity. Qed.
Example exp_three : forall a, exp 3 a = (a * (a * a))%type.
Proof. reflexivity. Qed.

Lemma exp_S_iso : forall a n, exp (S n) a ≅ a * exp n a.
Proof.
  induction n;
  rewrite ?mul_one_iso;
  reflexivity.
Qed.
Hint Rewrite exp_S_iso : isos.

Add Parametric Morphism : exp
  with signature (eq ==> isomorphic ==> isomorphic)
    as exp_isomorphism.
Proof.
  intros n a t H.
  induction n.
    reflexivity.
  rewrite !exp_S_iso, IHn, H.
  reflexivity.
Qed.

Theorem exp_plus_iso : forall a n m, exp (n + m) a ≅ exp n a * exp m a.
Proof.
  induction n; intros.
  rewrite one_mul_iso.
    reflexivity.
  autorewrite with isos.
  rewrite IHn, mul_assoc_iso.
  reflexivity.
Qed.
Hint Rewrite exp_plus_iso : isos.

(** Lists *)

Theorem list_cons_iso : forall a, one + (a * list a) ≅ list a.
Proof.
  intros.
  exists (fun p => match p with
                   | inl _ => nil
                   | inr (x, xs) => cons x xs
                   end).
  exists (fun p => match p with
                   | nil => inl tt
                   | cons x xs => inr (x, xs)
                   end).
  extensionalize A B C.
Qed.
Hint Rewrite list_cons_iso : isos.

Lemma iso_impl : @subrelation Prop isomorphic Basics.impl.
Proof.
  unfold subrelation, predicate_implication, pointwise_lifting.
  intros A B.
  unfold Basics.impl.
  intros H x.
  do 2 destruct H.
  exact (x0 x).
Qed.

Definition exp_to_list {a n} (l : exp n a) : list a.
Proof.
  induction n; simpl; intros.
    exact nil.
  destruct n.
    exact (cons l nil).
  destruct l.
  exact (cons a0 (IHn e)).
Defined.

Definition list_to_exp {a} (l : list a) : exp (length l) a.
Proof.
  induction l; simpl; auto.
    constructor.
  destruct (length l).
    exact a0.
  exact (a0, IHl).
Defined.

Theorem list_exp_iso : forall a : Type, { n : nat & exp n a } ≅ list a.
Proof.
  intros.
  exists (fun p : { n : nat & exp n a } =>
            match p with
            | existT _ xs => exp_to_list xs
            end).
  exists (fun l => existT _ (length l) (list_to_exp l)).
  unfold comp, id.
  split.
    extensionality l.
    induction l; trivial.
    simpl.
Abort.

(** Identity *)

Theorem identity_iso : forall (A : Type), Identity A ≅ A.
Proof. reflexivity. Qed.
Hint Rewrite identity_iso : Isos.

Theorem Identity_representable : representable Identity.
Proof.
  intro a.
  exists unit.
  exists (fun k => k tt).
  exists (fun i u => i).
  extensionalize A B C.
Qed.

(** Yoneda *)

Import MonadLaws.

Theorem Yoneda_iso : forall `{FunctorLaws f} a, Yoneda f a ≅ f a.
Proof.
  intros.
  exists (fun k => k _ id).
  exists (fun x _ f => fmap f x).
  extensionalize A B C.
    rewrite fmap_id0; trivial.
  Import YonedaLaws.
  exact (Yoneda_parametricity _ _ _ _ _ _).
Qed.
Hint Resolve Yoneda_iso : isos.

(* Given a pair (y -> a, f y), and a function g : y -> x, then the pair
    (id, fmap g c) is informationally equivalent to the pair (g, c). *)
Axiom Coyoneda_parametricity : forall `{Functor f} x y (g : y -> x) (c : f y),
  EqdepFacts.eq_dep Type (fun r : Type => ((r -> x) * f r)%type)
    x (id, fmap g c) y (g, c).

Lemma Coyoneda_iso : forall `{FunctorLaws f} x,
  { r : Type & ((r -> x) * f r)%type } ≅ f x.
Proof.
  intros.
  exists (fun p => match p with existT e (x, H) => fmap x H end).
  exists (fun v : f x => existT _ x (id, v)).
  extensionalize A B C.
    rewrite fmap_id0; trivial.
  apply EqdepFacts.eq_dep_eq_sigT.
  exact (Coyoneda_parametricity _ _ _ _).
Qed.
Hint Resolve Coyoneda_iso : isos.

(** Cont *)

Theorem Cont_iso : forall A, (forall r, Cont r A) ≅ A.
Proof.
  intros.
  exists (fun k => k _ id).
  exists (fun x _ k => k x).
  extensionalize A B C.
  extensionality k.
  apply Cont_parametricity.
Qed.
Hint Rewrite Cont_iso : isos.

(** Reader *)

Definition Reader (e : Type) (a : Type) := e -> a.

(** Codensity *)

Definition Codensity m a := forall r : Type, (a -> m r) -> m r.

Theorem Codensity_Reader_State_iso : forall e a,
  Codensity (Reader e) a ≅ State e a.
Proof.
  intros.
  unfold Codensity, Reader, State.
  rewrite <- (Cont_iso (a * e)), exp_exp_sym_dep_iso.
  apply iso_ext; intros.
  unfold Cont.
  rewrite exp_mul_iso, exp_exp_sym_iso.
  reflexivity.
Qed.

(** Haskell types *)

Theorem Maybe_Either_iso : forall a, Either unit a ≅ Maybe a.
Proof.
  intros.
  exists (fun p => match p with | inl x => Nothing
                                | inr x => Just x end).
  exists (fun p => match p with | Nothing => inl tt
                                | Just x  => inr x end).
  extensionalize A B C.
Qed.

Require Import Hask.Data.Functor.Fix.
Require Import Hask.Control.Monad.Freer.

Theorem Free_Fix_iso : forall `{Functor f} a, Fix (Either a ∘ f) ≅ Free f a.
Proof.
  unfold Fix, Free, comp.
  intros.
  apply iso_ext; intros.
  rewrite exp_exp_sym_dep_iso.
  unfold isomorphic.
  exists (fun (k : (forall x0 : Type, (x0 -> x) -> a + f x0 -> x) -> x)
              (g : forall x0 : Type, (x0 -> x) -> f x0 -> x)
              (h : a -> x) =>
            k (fun x j p =>
                 match p with
                 | inl a => h a
                 | inr f => g x j f
                 end)).
  exists (fun (k : (forall x0 : Type, (x0 -> x) -> f x0 -> x) -> (a -> x) -> x)
              (g : forall x0 : Type, (x0 -> x) -> a + f x0 -> x) =>
            k (fun x j f => g x j (inr f))
              (fun a => g False (False_rect _) (inl a))).
  extensionalize A B C.
  f_equal.
  extensionality x0.
  extensionality j.
  extensionality p.
  destruct p; trivial.
Abort.

Require Import Hask.Control.Monad.Free.

Theorem Free_Fix_iso : forall `{Functor f} a, Fix (Either a ∘ f) ≅ Free f a.
Proof.
  intros.
  exists
    (fun (k : forall r : Type, (forall x, (x -> r) -> a + f x -> r) -> r) =>
       k (Free f a)
         (fun _ h p =>
            match p return Free f a with
            | inl x => Pure x
            | inr x => Join h x
            end)).
  (* exists *)
  (*   (fun p r (k : forall x : Type, (x -> r) -> a + f x -> r) => *)
  (*      let fix go (p : Free f a) {struct p} : r := *)
  (*          match p return r with *)
  (*          | Pure x     => k r id (inl x) *)
  (*          | Join t h x => k t (go ∘ h) (inr x) *)
  (*          end in *)
  (*      go p). *)
  (* extensionalize A B C. *)
Abort.

(** Lenses *)

Axiom Lens_parametricity :
  forall `{Functor f} `{Functor g} (eta : forall a, f a -> g a)
         `(c : a -> f b) `(lens : Lens s t a b),
    eta t ∘ lens f H c = lens g H0 (eta b ∘ c).

Definition IStore a b t := (a * (b -> t))%type.

Instance IStore_Functor {a b} : Functor (IStore a b) := {
  fmap := fun _ _ f x => match x with
                           (a, k) => (a, fun b => f (k b))
                         end
}.

Program Instance IStore_FunctorLaws {a b} : FunctorLaws (IStore a b).
Obligation 1.
  extensionality p.
  destruct p.
  reflexivity.
Qed.
Obligation 2.
  extensionality p.
  destruct p.
  reflexivity.
Qed.

Definition Nat (f g : Type -> Type) := forall x : Type, f x -> g x.

Infix "⟹" := Nat (at level 100).

Import MonadLaws.

Lemma IStore_Yoneda_iso : forall `{FunctorLaws f} a b,
  (IStore a b ⟹ f) ≅ a -> f b.
Proof.
  intros.
  unfold IStore.
  pose proof (@Yoneda_iso f H H0 b).
  unfold Yoneda in H1.
  rewrite <- H1.
  assert ((a -> forall r : Type, (b -> r) -> f r) ≅
          (forall r : Type, a -> (b -> r) -> f r)).
    exists (fun k r a g => k a r g).
    exists (fun k a r g => k r a g).
    extensionalize A B C.
  rewrite H2.
  apply iso_ext; intros.
  rewrite exp_mul_iso.
  reflexivity.
Qed.

Lemma IStore_fun_iso : forall s t a b,
  (IStore s t ⟹ IStore a b) ≅ (s -> (Basics.arrow t ⟹ IStore a b)).
Proof.
  intros.
  unfold Basics.arrow, Nat.
  rewrite exp_exp_sym_dep_iso.
  apply iso_ext; intros.
  unfold IStore.
  rewrite exp_mul_iso.
  reflexivity.
Qed.

Lemma CoYoneda_embedding_iso : forall a b : Type,
  (forall x : Type, (a -> x) -> (b -> x)) ≅ (b -> a).
Proof.
  intros.
  rewrite <- (Cont_iso a).
  rewrite exp_exp_sym_dep_iso.
  apply iso_ext; intros.
  rewrite exp_exp_sym_iso.
  reflexivity.
Qed.

Axiom Yoneda_embedding_parametricity :
  forall `(k : forall x : Type, (x -> a) -> x -> b)
         `(C : x -> a) (x0 : x),
  k a id (C x0) = k x C x0.

Lemma Yoneda_embedding_iso : forall a b : Type,
  (forall x : Type, (x -> a) -> (x -> b)) ≅ (a -> b).
Proof.
  intros.
  unfold isomorphic.
  exists (fun (f : forall x : Type, (x -> a) -> x -> b) => f _ id).
  exists (fun (f : a -> b) x k x0 => f (k x0)).
  extensionalize A B C.
  extensionality x0.
  apply Yoneda_embedding_parametricity.
Qed.

Lemma IStore_IStore_iso : forall s t a b,
  (forall `{Functor f}, (IStore a b ⟹ f) -> (IStore s t ⟹ f))
    ≅ (IStore s t ⟹ IStore a b).
Proof.
  intros.
  rewrite IStore_Yoneda_iso.
  unfold IStore, Nat.
Abort.

Lemma Lens_IStore_iso : forall s t a b,
  Lens s t a b ≅ (IStore s t ⟹ IStore a b).
Proof.
Abort.

Lemma Lens_pair_iso : forall (s t a b : Type),
  Lens s t a b ≅ (s -> a) * (s -> b -> t).
Proof.
  intros.
  unfold Lens.
  rewrite <- mul_exp_iso.
  pose proof (@IStore_Yoneda_iso
                (fun t => (a * (b -> t))%type) _ _ s t).
  simpl in H.
  rewrite <- H.
  unfold IStore.
  assert ((forall f : Type -> Type, Functor f -> (a -> f b) -> s -> f t)
          ≅ (s -> forall f : Type -> Type, Functor f -> (a -> f b) -> f t)).
    exists (fun k s f H g => k f H g s).
    exists (fun k f H g s => k s f H g).
    extensionalize A B C.
  rewrite H; clear H.
  exists (fun (k : Lens s t a b) s =>
            (@k (Const a) _ id s,
             fun b => @k Identity _ (const b) s)).
  exists (fun (k : s -> a * (b -> t)) =>
            fun `{Functor f} g s =>
              match k s with (a, h) => fmap[f] h (g a) end).
  unfold comp, id. simpl.
  split.
    extensionality k.
    extensionality u.
    destruct (k u).
    f_equal.
  extensionality l.
  extensionality f.
  extensionality H.
  extensionality g.
  extensionality u.
Abort.

(** Church encodings *)

(* See ../Data/Functor/Kan.v for Lan, Lan_final, and Lan_final_parametricity *)

Lemma Lan_alg_iso : forall f g a,
  Lan f g a -> a ≅ forall x, (f x -> a) -> g x -> a.
Proof.
  intros.
  unfold Lan.
  rewrite exp_sigT_iso.
  apply iso_ext; intros.
  rewrite exp_mul_iso.
  reflexivity.
Qed.

Corollary Lan_id_f_iso : forall `{FunctorLaws f} a, Lan id f a ≅ f a.
Proof. exact @Coyoneda_iso. Qed.

Lemma Coyoneda_alg_iso : forall `{FunctorLaws f} x,
  (forall r : Type, (r -> x) -> f r -> x) ≅ f x -> x.
Proof.
  intros.
  rewrite <- Lan_alg_iso, Lan_id_f_iso.
  reflexivity.
Qed.

Inductive Foo (a b : Type) :=
  | mkFoo : a -> b -> Foo a b
  | mkBar : a -> a -> Foo a b -> Foo a b
  | mkBaz : Foo a b.

Lemma Foo_Algebra : forall a b,
  Foo a b ≅ (a * b) + (a * a * Foo a b) + unit.
Proof.
  intros.
  exists (fun f => match f with
                   | mkFoo a b     => inl (inl (a, b))
                   | mkBar a1 a2 r => inl (inr (a1, a2, r))
                   | mkBaz         => inr tt
                   end).
  exists (fun p => match p with
                   | inl (inl (a, b))      => mkFoo _ _ a b
                   | inl (inr (a1, a2, r)) => mkBar _ _ a1 a2 r
                   | inr tt                => mkBaz _ _
                   end).
  extensionalize A B C.
Qed.

Inductive FooF (a b r : Type) :=
  | mkFooF : a -> b -> FooF a b r
  | mkBarF : a -> a -> r -> FooF a b r
  | mkBazF : FooF a b r.

(*
Definition wrap_FooF {a b} (x : FooF a b (Fix (FooF a b))) : Fix (FooF a b) :=
  fun r k => k (Fix (FooF a b)) (fun z => z r k) x.
*)

Instance FooF_Functor (a b : Type) : Functor (FooF a b) := {
  fmap := fun _ _ f x =>
            match x with
            | mkFooF a b => mkFooF _ _ _ a b
            | mkBarF a b v => mkBarF _ _ _ a b (f v)
            | mkBazF => mkBazF _ _ _
            end
}.

Program Instance FooF_FunctorLaws (a b : Type) : FunctorLaws (FooF a b).
Obligation 1. extensionalize A B C. Qed.
Obligation 2. extensionalize A B C. Qed.

Lemma FooF_Algebra : forall a b r,
  FooF a b r ≅ (a * b) + (a * a * r) + unit.
Proof.
  intros.
  exists (fun f => match f with
                   | mkFooF a b     => inl (inl (a, b))
                   | mkBarF a1 a2 r => inl (inr (a1, a2, r))
                   | mkBazF         => inr tt
                   end).
  exists (fun p => match p with
                   | inl (inl (a, b))      => mkFooF _ _ _ a b
                   | inl (inr (a1, a2, r)) => mkBarF _ _ _ a1 a2 r
                   | inr tt                => mkBazF _ _ _
                   end).
  extensionalize A B C.
Qed.

Definition Foo_to_FooF (a b : Type) (x : Foo a b) : Fix (FooF a b) :=
  fun r k =>
    k r id (let fix go x :=
                match x with
                | mkFoo a b   => mkFooF _ _ _ a b
                | mkBar x y v => mkBarF _ _ _ x y (k r id (go v))
                | mkBaz       => mkBazF _ _ _
                end in
            go x).

Definition FooF_to_Foo (a b : Type) (x : Fix (FooF a b)) : Foo a b :=
  x (Foo a b) (fun x k f =>
                 match fmap[FooF a b] k f with
                 | mkFooF a b   => mkFoo _ _ a b
                 | mkBarF a b v => mkBar _ _ a b v
                 | mkBazF       => mkBaz _ _
                 end).

Lemma FooF_Foo_eq : forall a b x,
  FooF_to_Foo a b (Foo_to_FooF a b x) = x.
Proof.
  intros.
  induction x; simpl; auto.
  unfold Foo_to_FooF, FooF_to_Foo; simpl.
  f_equal.
  destruct x; auto.
Qed.

Lemma Foo_FooF_eq : forall a b x,
  Foo_to_FooF a b (FooF_to_Foo a b x) = x.
Proof.
  intros.
  extensionality r.
  extensionality h.
Admitted.

Lemma Foo_Fix_FooF : forall a b,
  Foo a b ≅ Fix (FooF a b).
Proof.
  intros.
  exists (Foo_to_FooF a b).
  exists (FooF_to_Foo a b).
  unfold comp.
  split; extensionality x.
    exact (Foo_FooF_eq a b x).
  exact (FooF_Foo_eq a b x).
Qed.

Lemma Church_Foo : forall a b,
  Foo a b ≅ (forall r, (a -> b -> r) -> (a -> a -> r -> r) -> r -> r).
Proof.
  intros.
  rewrite Foo_Fix_FooF; unfold Fix.
  apply iso_ext; intros.
  rewrite Coyoneda_alg_iso,
          FooF_Algebra,
          exp_add_iso,
          exp_one_iso,
          exp_exp_sym_iso,
          exp_add_iso,
          !exp_mul_iso,
          exp_exp_sym_iso.
  apply f_exp_iso.
  rewrite exp_exp_sym_iso.
  reflexivity.
Qed.

(*
Lemma Lan_final_iso : forall f g a,
  Lan f g a ≅ Lan_final f g a.
Proof.
  intros.
  exists (fun p r k => match p with existT e (h, x) => k e h x end).
  exists (fun (k : forall r : Type,
                     (forall x : Type, (f x -> a) -> g x -> r) -> r) =>
            k (Lan f g a) (fun e h x => existT _ e (h, x))).
  extensionalize k r h.
  apply (Lan_final_parametricity
           a _ r _ _ k
           (fun e n x => existT _ e (n, x))
           (fun x : Lan f g a =>
              match x with
                existT e (n, x) => h e n x
              end)).
Qed.
*)

(* Algebras and final encodings *)

Lemma finenc_zero : zero ≅ (forall r, r).
Proof.
  intros.
  exists (False_rect _).
  exists (fun f => f False).
  extensionalize A B C.
  destruct (A False).
Qed.

Axiom id_parametricity : forall (f : forall r, r -> r), f = @id.

Lemma finenc_one : one ≅ (forall r, r -> r).
Proof.
  intros.
  exists (fun u r => id).
  exists (fun _ => tt).
  extensionalize A B C.
  rewrite (@id_parametricity A).
  reflexivity.
Admitted.               (* jww (2016-02-23): universe inconsistency! *)

Lemma finenc_a : forall a,
  a ≅ (forall r, (a -> r) -> r).
Proof.
  intros.
  rewrite <- (Cont_iso a).
  apply iso_ext; intros.
  unfold Cont.
  reflexivity.
Qed.

Lemma finenc_a_plus_b : forall a b,
  a + b ≅ (forall r, (a -> r) -> (b -> r) -> r).
Proof.
  intros.
  rewrite <- (Cont_iso (a + b)).
  apply iso_ext; intros.
  unfold Cont.
  rewrite exp_add_iso.
  reflexivity.
Qed.

Lemma finenc_a_times_b : forall a b,
  a * b ≅ (forall r, (a -> b -> r) -> r).
Proof.
  intros.
  rewrite <- (Cont_iso (a * b)).
  apply iso_ext; intros.
  unfold Cont.
  rewrite exp_mul_iso.
  reflexivity.
Qed.

Program Instance List_Alg_Functor : Functor (fun r => one + a * r)%type := {
  fmap := fun _ _ f x =>
            match x with
            | inl tt => inl tt
            | inr (a, r) => inr (a, f r)
            end
}.

Program Instance List_Alg_FunctorLaws : FunctorLaws (fun r => one + a * r)%type.
Obligation 1. extensionalize A B C. Qed.
Obligation 2. extensionalize A B C. Qed.

Lemma finenc_list : forall a,
  Fix (fun r => one + (a * r))%type ≅ (forall r, r -> (a -> r -> r) -> r).
Proof.
  intros.
  unfold Fix.
  apply iso_ext; intros.
  rewrite (@Coyoneda_alg_iso (fun r => one + a * r)%type).
  autorewrite with isos.
    reflexivity.
  exact List_Alg_FunctorLaws.
Qed.
