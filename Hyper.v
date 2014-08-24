Require Import Category.
Require Import Functor.

Set Implicit Arguments.

Close Scope nat_scope.

(* Formalization and exploration of hyper-functions. *)

Reserved Notation "f << h" (at level 68, left associativity).

Definition const {a b} (x : a) (_ : b) := x.

CoInductive stream (A : Type) : Type :=
  | Cons : A -> stream A -> stream A.

CoFixpoint stream_map {A B} (f : A -> B) (s : stream A) : stream B :=
  match s with
    | Cons x xs => Cons (f x) (stream_map f xs)
  end.

(* Hyperfunctions form a category, which when equipped with an embedding
   functor allow us to extend the set of operations by run and connect. *)

Section Hyperfunctions.

Context `(H : Category).
Context `(F : @Functor Sets H).

(* CoFixpoint fixpoint {a} (f : a -> a) : a := f (fixpoint f). *)

Class Hyperfunction := {
    run     : forall {a}, (F a ~> F a) -> stream a;
    connect : forall {a b}, (a -> b) -> (F a ~> F b) -> (F a ~> F b)
      where "f << h" := (connect f h);

    self {a} : (F a ~> F a) := fmap id;
    invoke {a b} (f : F a ~> F b) (g : F b ~> F a) : stream b := run (f ∘ g);
    base {a b} (k : b) : (F a ~> F b) := fmap (const k);
    project {a b} (q : F a ~> F b) (x : a) : stream b := invoke q (base x);

    (* hyper_law_fix : forall f, run (fmap f) = fixpoint f; *)

    hyper_law_distr : forall {a b c} (f : b -> c) (g : a -> b) p q,
      (f << p) ∘ (g << q) = (@compose Sets _ _ _ f g) << (p ∘ q);

    hyper_law_lift : forall {a b} (f : a -> b), fmap f = f << fmap f;

    hyper_law_run : forall {a b} (f : a -> b) p q,
       run ((f << p) ∘ q) = stream_map f (run (q ∘ p))
}.

Definition mapH {a' b' a b} (r : a' -> a) (s : b -> b')
  (f : F a ~> F b) : (F a' ~> F b') := fmap s ∘ f ∘ fmap r.

End Hyperfunctions.

Coercion project : Hyperfunction >-> Funclass.

Inductive HMachine (a b : Type) : Type :=
  | Hide : forall u, (u -> (b + ((a -> b) * u))) -> u -> HMachine a b.

Arguments Hide [a] [b] [u] _ _.

Definition lift {a b u} (seed : u) (f : a -> b) : HMachine a b :=
  Hide (fun x => inr (f, x)) seed.

Definition hcompose {a b c} (gm : HMachine b c) (gm' : HMachine a b)
  : HMachine a c :=
  match gm with
  | Hide _ g x => match gm' with
    | Hide _ g' x' => Hide (fun zz => match zz with
      | (z, z') => match g z with
        | inl n => inl n
        | inr (f, y) => match g' z' with
          | inl m => inl (f m)
          | inr (f', y') => inr (@compose Sets _ _ _ f f', (y, y'))
          end
        end
      end) (x, x')
    end
  end.

Program Instance HMachine_Category : Category := {
    ob      := @ob Sets;
    hom     := HMachine;
    id      := fun X => lift tt (@id Sets X);
    compose := @hcompose
}.
Obligation 1.
  unfold hcompose, lift.
  destruct f. simpl.
Admitted.
Obligation 2.
  unfold hcompose, lift.
  destruct f. simpl.
Admitted.
Obligation 3.
  unfold hcompose.
  destruct f. destruct g. destruct h.
  simpl.
  apply f_equal2 with pair_assoc.
Defined.

CoFixpoint HMachine_run {a : Type} (h : HMachine a a) : stream (a -> a) :=
  match h with
  | f :<<: fs => Cons f (HMachine_run fs)
  end.

Program Instance HMachine_Functor : Sets ⟶ HMachine_Category := {
    fobj := fun x => x;
    fmap := @lift
}.
Obligation 2.
  apply hstream_equality.
  rewrite (frob_eq (hcompose (lift f) (lift g))).
  rewrite (frob_eq (lift (λ x : X, f (g x)))).
  simpl. destruct (lift f). destruct (lift g).
  destruct h. destruct h0.
  revert z z0 h y y0 h0. cofix.
  intros. constructor.
  destruct h. destruct h0.
  specialize (HMachine_Functor_obligation_2 z0 z1 h y0 y1 h0).
  rewrite (frob_eq (hcompose _ _)).
  rewrite (frob_eq (lift _)).
  simpl. (* apply HMachine_Functor_obligation_2. *)
Admitted.

Program Instance HMachine_Hyper : Hyperfunction HMachine_Functor := {
    run := fun X => @HMachine_run X
}.
Obligation 4.
  unfold HMachine_Hyper_obligation_1.
  destruct p. destruct q.
  assert (b0 (a0 (f aseed)) =
         (@compose Sets _ _ _ (@compose Sets _ _ _ b0 a0) f) aseed).
    auto. rewrite H. clear H.
  assert (f (a0 (b0 aseed)) =
         (@compose Sets _ _ _ f (@compose Sets _ _ _ a0 b0)) aseed).
    auto. rewrite H. clear H.
Admitted.

Theorem hstream_functor_faithful : forall {a b} (f g : a -> b) (seed : b),
  lift f = lift g -> f = g.
Proof.
  intros.
  assert (forall x, f x = project seed (lift f) x). auto.
  rewrite H in H0.
  extensionality x.
  rewrite H0. auto.
Qed.
