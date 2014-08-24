Require Import Category.
Require Import Functor.

Set Implicit Arguments.

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

Coercion project : Hyperfunction >-> Funclass.

CoInductive HStream (a b : Type) : Type :=
  | HCons : (a -> b) -> HStream a b -> HStream a b.

Arguments HCons [a] [b] _ _.

Infix ":<<:" := HCons (at level 98, left associativity).

CoInductive hstream_eq {a b} : HStream a b -> HStream a b -> Prop :=
  | HStream_eq :
      forall h t1 t2, hstream_eq t1 t2 -> hstream_eq (h :<<: t1) (h :<<: t2).

Definition frob {a b} (s : HStream a b) : HStream a b :=
  match s with
    | h :<<: t => h :<<: t
  end.

Theorem frob_eq : forall {a b} (s : HStream a b), s = frob s.
Proof. destruct s; reflexivity. Defined.

CoFixpoint lift {a b} (f : a -> b) : HStream a b := f :<<: lift f.

CoFixpoint hcompose {a b c}
  (hf : HStream b c) (hg : HStream a b) : HStream a c :=
  match hf with
  | f :<<: fs => match hg with
    | g :<<: gs => (@compose Sets _ _ _ f g) :<<: (hcompose fs gs)
    end
  end.

End Hyperfunctions.

Infix ":<<:" := HCons (at level 98, left associativity).

Hypothesis hstream_equality : forall {a b} (x y : HStream a b),
  hstream_eq x y -> x = y.

Program Instance HStream_Category : Category := {
    ob := @ob Sets;
    hom := HStream;
    id := fun X => lift (@id Sets X);
    compose := @hcompose
}.
Obligation 1.
  apply hstream_equality.
  rewrite (frob_eq (hcompose f (lift (fun x : A => x)))).
  rewrite (frob_eq f).
  simpl. destruct f. simpl.
  revert b f. cofix.
  intros. constructor. destruct f.
  rewrite (frob_eq (hcompose _ (lift (fun x : A => x)))).
  rewrite (frob_eq f).
  simpl. apply HStream_Category_obligation_1.
Defined.
Obligation 2.
  apply hstream_equality.
  rewrite (frob_eq (hcompose (lift (fun x : B => x)) f)).
  rewrite (frob_eq f).
  simpl. destruct f. simpl.
  revert b f. cofix.
  intros. constructor. destruct f.
  rewrite (frob_eq (hcompose (lift (fun x : B => x)) _)).
  rewrite (frob_eq f).
  simpl. apply HStream_Category_obligation_2.
Defined.
Obligation 3.
  apply hstream_equality.
  rewrite (frob_eq (hcompose f (hcompose g h))).
  rewrite (frob_eq (hcompose (hcompose f g) h)).
  simpl. destruct f. destruct g. destruct h. simpl.
  revert d f c g b h. cofix.
  intros. constructor.
  destruct f. destruct g. destruct h.
  rewrite (frob_eq (hcompose _ (hcompose _ _))).
  rewrite (frob_eq (hcompose (hcompose _ _) _)).
  simpl. apply HStream_Category_obligation_3.
Defined.

CoFixpoint HStream_run {a : Type} (h : HStream a a) : stream (a -> a) :=
  match h with
  | f :<<: fs => Cons f (HStream_run fs)
  end.

Typeclasses Transparent HStream_Category.

Program Instance HStream_Functor : Sets ⟶ HStream_Category := {
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
  specialize (HStream_Functor_obligation_2 z0 z1 h y0 y1 h0).
  rewrite (frob_eq (hcompose _ _)).
  rewrite (frob_eq (lift _)).
  simpl. (* apply HStream_Functor_obligation_2. *)
Admitted.

Program Instance HStream_Hyper : Hyperfunction HStream_Functor := {
    run := fun X => @HStream_run X
}.
Obligation 4.
  unfold HStream_Hyper_obligation_1.
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
