(* This file formalizes the proofs from Duncan Coutts' thesis:

   "Stream Fusion: Practical shortcut fusion for coinductive sequence types".

   http://community.haskell.org/~duncan/thesis.pdf
*)

Require Export Coq.Unicode.Utf8.
Require Import Coq.Init.Datatypes.
Require Import Coq.Program.Tactics.
Require Import FunctionalExtensionality.
Require Import Hask.Prelude.
Require Import Hask.Control.Lens.
Require Import Hask.Control.Monad.

(* Set Universe Polymorphism. *)

Generalizable All Variables.

Definition FreeT (f m : Type -> Type) (a : Type) :=
  forall r, (a -> m r) -> (forall x, (x -> m r) -> f x -> m r) -> m r.

Program Instance FreeT_Functor {f m} : Functor (FreeT f m) := {
  fmap := fun _ _ f k => fun _ a fr => k _ (a \o f) fr
}.

Program Instance FreeT_Applicative {f m} : Applicative (FreeT f m) := {
  pure := fun _ a => fun _ k _ => k a;
  ap   := fun _ _ fk ak => fun _ b fr =>
    fk _ (fun e => ak _ (fun d => b (e d)) fr) fr
}.

Program Instance FreeT_Monad {f m} : Monad (FreeT f m) := {
  join := fun _ x => fun _ k g => undefined
}.

Inductive ProxyF a' a b' b r :=
  | Request of a' & (a  -> r)
  | Respond of b  & (b' -> r).

Arguments Request {a' a b' b r} _ _.
Arguments Respond {a' a b' b r} _ _.

Definition Proxy a' a b' b m r := FreeT (ProxyF a' a b' b) m r.

Definition runEffect `{Monad m} `(p : Proxy False unit unit False m r) : m r :=
  p _ pure $ fun _ k x => match x with
    | Request _ f => k (f tt)
    | Respond _ f => k (f tt)
    end.

Definition respond `{Monad m} `(z : a) {x' x a'} : Proxy x' x a' a m a' :=
  fun _ k g => g _ id $ Respond z k.

Definition Producer  b m r := Proxy False unit unit b m r.
Definition Producer' b m r := forall x' x, Proxy x' x unit b m r.

Definition yieldxx `{Monad m} {a} (z : a) : Producer' a m unit :=
  fun _ _ => respond z.

Definition yield `{Monad m} {a x' x} (z : a) : Proxy x' x unit a m unit :=
  @yieldxx m _ a z x' x.

Definition forP `{Monad m} `(p0 : Proxy x' x b' b m a')
  `(fb : b -> Proxy x' x c' c m b') : Proxy x' x c' c m a' :=
  fun _ k g => p0 _ k $ fun _ h x => match x with
    | Request x' fx  => g _ h $ Request x' fx
    | Respond b  fb' => fb b _ (h \o fb') g
    end.

Notation "x //> y" := (forP x y) (at level 60).

Definition each `{Monad m} {a} : seq a -> Producer a m unit :=
  mapM_ yield.
  (* @mapM_ (FreeT (ProxyF False unit unit a) m) *)
  (*        (@FreeT_Monad (ProxyF False unit unit a) m) _ _ yield. *)

Definition toListM `{Monad m} `(p : Producer a m unit) : m (seq a) :=
  p _ (fun _ => pure [::]) $ fun X h p => match p with
    | Request v f  => h (f tt)
    | Respond x f => @fmap m _ _ _ (cons x) (h (f tt))
    end.

Inductive Identity (a : Type) := Id of a.

Definition runIdentity `(x : Identity a) : a :=
  match x with Id y => y end.

Program Instance Identity_Functor : Functor Identity := {
  fmap := fun _ _ f x => Id _ (f (runIdentity x))
}.

Program Instance Identity_Applicative : Applicative Identity := {
  pure := fun _ => Id _;
  ap := fun _ _ f x => Id _ (runIdentity f (runIdentity x))
}.

Program Instance Identity_Monad : Monad Identity := {
  join := fun _ => runIdentity
}.

Module PipesLaws.

Include MonadLaws.

Section Examples.

Context `{H : Monad m}.
Context `{HL : MonadLaws m}.

Axiom fmap_cps : forall `{Functor f} a b c (k : forall r, (a -> r) -> f r)
  (g : b -> c) (h : a -> b), fmap g (k _ h) = k _ (g \o h).

(* Lemma toListM_cons : forall a (x : a) xs, *)
(*   toListM (each (x :: xs)) = fmap (cons x) (toListM (each xs)). *)
(* Proof. *)
(*   move=> a x xs. *)
(*   elim: xs => //= [|y ys IHys] in x *. *)
(*     rewrite /each /=. *)
(*     admit. *)
(*   rewrite /each /=. *)

Example toListM_each : forall a (xs : seq a), toListM (each xs) = pure xs.
Proof.
  move=> a xs.
  elim: xs => //= [x xs IHxs].
  rewrite -ap_homo -IHxs ap_fmap_ext.
  rewrite /each /mapM_ /= -/mapM_ -/each.
  rewrite /toListM.

(* main :: IO () *)
(* main = do *)
(*     runEffect $ for (each [1..4 :: Int]) (lift . print) *)
(*     runEffect $ for stdinLn (lift . putStrLn) *)

Require Import Endo.
Require Import Iso.

Close Scope nat_scope.

(* Section 2.2.3 *)

Definition NatF (a : Type) := unit + a.

(* This does not work in Coq, because of the strict positivity requirement. *)
(* Inductive Fix (F : Type -> Type) := outF : F (Fix F) -> Fix F. *)

Definition μNat := μ NatF.

Definition zero : μNat := λ a (X : NatF a   → a), X (inl tt).
Definition one  : μNat := λ a (X : unit + a → a), X (inr (X (inl tt))).

Definition ChurchNat := ∀ a, a → (a → a) → a.

Inductive Nat :=
  | Z : Nat
  | S : Nat -> Nat.

(*
Program Instance nat_is_muNat : Nat ≅ μNat.
Obligation 1.
  compute in *. intros.
  induction H; apply X.
    left. constructor.
  right. apply IHNat.
Defined.
Obligation 2.
  compute in *. intros.
  apply X. intros.
  destruct H.
    apply Z.
  apply (S n).
Defined.
Obligation 3.
  unfold nat_is_muNat_obligation_1.
  unfold nat_is_muNat_obligation_2.
  unfold compose.
  extensionality x.
  induction x; auto.
  simpl. rewrite IHx.
  reflexivity.
Defined.
Obligation 4.
  unfold nat_is_muNat_obligation_1.
  unfold nat_is_muNat_obligation_2.
  unfold compose.
  extensionality x.
  extensionality a.
  extensionality X.
  unfold id.
  compute in x.
  compute.
Abort.
*)

Program Instance nat_is_Church : μNat ≅ ChurchNat.
Obligation 1.
  compute in *. intros.
  apply X. intros.
  induction X2 as [| H].
    apply X0.                   (* Z case *)
  apply X1. apply H.            (* S case *)
Defined.
Obligation 2.
  compute in *. intros.
  apply X; intros; apply X0.
    left. constructor.          (* Z case *)
  right. apply X1.              (* S case *)
Defined.
Obligation 3.
  compute.
  extensionality H.
  extensionality a.
  extensionality X0.
  f_equal.
  extensionality X2.
  destruct X2.
    destruct u. reflexivity.
  reflexivity.
Qed.

Program Instance sum_distributive : ∀ a b c, ((a + b) → c) ≅ ((a → c) * (b → c)).
Solve All Obligations using auto.
Obligation 2. destruct X0; auto. Defined.
Obligation 3.
  compute.
  extensionality x.
  extensionality n.
  destruct n; auto.
Qed.
Obligation 4.
  compute.
  extensionality x.
  destruct x. auto.
Qed.

Program Instance unit_impl : ∀ a, (unit → a) ≅ a.
Solve All Obligations using auto.
Obligation 1. apply X. constructor. Defined.
Obligation 3.
  compute.
  extensionality H.
  extensionality tt.
  destruct tt. reflexivity.
Qed.

Section F.
  Variable F : Type → Type.
  Context `{Functor F}.

(* Definition 2.2.1 *)
Definition fold : ∀ a, (F a → a) → μ F → a :=
  fun a => fun k => fun x => x a k.

(* Definition 2.2.2 *)
Definition build : (∀ a, (F a → a) → a) → μ F :=
  fun g => fun b => fun k => g b k.

Inductive nu : Type := unNu : ∀ a, a → (a → F a) → nu.

(* Definition 2.2.3 *)
Definition unfold : ∀ a, (a → F a) → a → nu :=
  fun a => fun k => fun s => unNu a s k.

(* Definition 2.2.4 *)
Definition unbuild : ∀ c, (∀ a, (a → F a) → a → c) → (nu → c) :=
  fun c => fun g => fun x => match x with
    unNu _ s k => g _ k s
  end.

(* Theorem 3.2.1 *)
Theorem fold_build_fusion : ∀ a k g, fold a k (build g) = g a k.
Proof. auto. Qed.

(* Theorem 3.2.2 *)
Theorem unbuild_unfold_fusion : ∀ c a k g s, unbuild c g (unfold a k s) = g a k s.
Proof. auto. Qed.

Lemma free_theorem_for_fold : ∀ A A' h k k',
  h ∘ k = k' ∘ fmap h → h ∘ fold A k = fold A' k'.
Proof.
  intros.
  unfold fold, compose.
  extensionality x.
  (* jww (2014-09-08): How to proceed from here? *)
Admitted.

Definition initial_algebra (y : F (μ F)) : μ F :=
  fun b (k : F b -> b) => k (fmap (fold b k) y).

(* Lemma 3.3.2 *)
Theorem ump_fold_1 : ∀ a (h : μ F → a) (k : F a → a),
  h = fold a k → h ∘ initial_algebra = k ∘ fmap h.
Proof.
  intros.
  rewrite H0.
  extensionality y.
  unfold compose, fold, initial_algebra.
  auto.
Qed.

(* Lemma 3.3.3 *)
Theorem ump_fold_2 : ∀ a (h : μ F → a) (k : F a → a),
  h ∘ initial_algebra = k ∘ fmap h → h = fold a k.
Proof.
  intros.
  pose (free_theorem_for_fold (μ F) a h initial_algebra k).
  pose proof H0.
  apply e in H0. clear e.
  rewrite <- H0.
  replace (fold (μ F) initial_algebra) with (@id (μ F)).
    rewrite comp_id_right. reflexivity.
  symmetry.
  replace h with (fold a k) in H0.
  unfold compose in H0.
  unfold fold at 1 in H0.
  unfold fold at 2 in H0.
  rewrite (eta_expansion (fold (μ F) initial_algebra)).
Admitted.
