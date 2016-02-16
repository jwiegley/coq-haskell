Require Import Hask.Ltac.
Require Import Hask.Prelude.
Require Import Hask.Control.Applicative.
Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.Cont.
Require Import Hask.Control.Monad.State.
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
  extensionalize A B C.
  - replace (from_x (to_x y1)) with ((from_x ∘ to_x) y1); trivial.
    rewrite H1.
    reflexivity.
  - replace (from_x0 (to_x0 y1)) with ((from_x0 ∘ to_x0) y1); trivial.
    rewrite H.
    reflexivity.
  - replace (to_x (from_x x1)) with ((to_x ∘ from_x) x1); trivial.
    rewrite H2.
    reflexivity.
  - replace (to_x0 (from_x0 x1)) with ((to_x0 ∘ from_x0) x1); trivial.
    rewrite H3.
    reflexivity.
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
  extensionalize A B C.
  - replace (from_x (to_x y1)) with ((from_x ∘ to_x) y1); trivial.
    rewrite H1.
    replace (from_x0 (to_x0 y2)) with ((from_x0 ∘ to_x0) y2); trivial.
    rewrite H.
    reflexivity.
  - replace (to_x (from_x x1)) with ((to_x ∘ from_x) x1); trivial.
    rewrite H2.
    replace (to_x0 (from_x0 x2)) with ((to_x0 ∘ from_x0) x2); trivial.
    rewrite H3.
    reflexivity.
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

Corollary exp_add_more_iso : forall a b c d,
  (d -> (a + b) -> c) -> c ≅ (d -> a -> c) -> (d -> b -> c) -> c.
Proof.
  intros.
  rewrite <- exp_mul_iso, mul_add_iso, exp_add_iso, !exp_mul_iso.
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
  apply Yoneda_parametricity.
Qed.
Hint Resolve Yoneda_iso : isos.

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

Lemma Lens_pair_iso : forall (s t a b : Type),
  Lens s t a b ≅ (s -> a) * (s -> b -> t).
Proof.
  intros.
  unfold Lens.
  rewrite <- mul_exp_iso.
  exists (fun (k : forall f : Type -> Type, Functor f
                     -> (a -> f b) -> s -> f t) s =>
            (k (Const a) _ id s,
             fun b => k Identity _ (const b) s)).
  exists (fun (k : s -> a * (b -> t))
              (f : Type -> Type) (H : Functor f) g s =>
            match k s with
              (a, h) => @fmap f H b t h (g a)
            end).
  extensionalize A B C.
  extensionality h.
  extensionality x.
Abort.