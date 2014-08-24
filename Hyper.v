Require Import Category.
Require Import Functor.

Set Implicit Arguments.

Close Scope nat_scope.

(* Formalization and exploration of hyper-functions. *)

Reserved Notation "f << h" (at level 53, left associativity).

Definition const {a b} (x : a) (_ : b) := x.

CoInductive stream (A : Type) : Type :=
  | Cons : A → stream A → stream A.

CoFixpoint stream_map {A B} (f : A → B) (s : stream A) : stream B :=
  match s with
    | Cons x xs => Cons (f x) (stream_map f xs)
  end.

(* Hyperfunctions form a category, which when equipped with an embedding
   functor allow us to extend the set of operations by run and connect. *)

Section Hyperfunctions.

Context `(H : Category).
Context `(F : @Functor Sets H).

(* CoFixpoint fixpoint {a} (f : a → a) : a := f (fixpoint f). *)

Definition fmap' {X Y} `(f : X → Y) := (@fmap Sets H F X Y f).

Class Hyperfunction := {
    run     : forall {a}, (F a ~> F a) → stream a;
    connect : forall {a b}, (a → b) → (F a ~> F b) → (F a ~> F b)
      where "f << h" := (connect f h);

    self {a} : (F a ~> F a) := fmap' (@id Sets a);
    invoke {a b} (f : F a ~> F b) (g : F b ~> F a) : stream b := run (f ∘ g);
    base {a b} (k : b) : (F a ~> F b) := fmap' (const k);
    project {a b} (q : F a ~> F b) (x : a) : stream b := invoke q (base x);

    (* hyper_law_fix : forall f, run (fmap' f) = fixpoint f; *)

    hyper_law_distr : forall {a b c} (f : b → c) (g : a → b) p q,
      (f << p) ∘ (g << q) ≈ (@compose Sets _ _ _ f g) << (p ∘ q);

    hyper_law_lift : forall {a b} (f : a → b), fmap' f ≈ f << fmap' f;

    hyper_law_run : forall {a b} (f : a → b) p q,
       run ((f << p) ∘ q) = stream_map f (run (q ∘ p))
}.

Definition mapH {a' b' a b} (r : a' → a) (s : b → b')
  (f : F a ~> F b) : (F a' ~> F b') := fmap' s ∘ f ∘ fmap' r.

End Hyperfunctions.

Coercion project : Hyperfunction >-> Funclass.

Inductive HMachine {u} (a b : Type) : Type :=
  | Hide : (u → (b + ((a → b) * u))) → u → HMachine a b.

Arguments Hide [u] [a] [b] _ _.

Definition lift {u a b} (seed : u) (f : a → b) : HMachine a b :=
  Hide (fun x => inr (f, x)) seed.

Definition hcompose {u a b c} (gm : @HMachine u b c) (gm' : @HMachine u a b)
  : HMachine a c :=
  match gm with
  | Hide g x => match gm' with
    | Hide g' x' => Hide (fun zz => match zz with
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

Definition HMachine_equiv {u a b} (x y : @HMachine u a b) : Prop :=
  match x with
  | Hide f0 u => match y with
    | Hide f1 u => f0 ≈ f1
    end
  end.

Program Instance HMachine_equivalence {u} (a b : Type)
  : Equivalence (@HMachine_equiv u a b).
Obligation 1.
  unfold Reflexive, HMachine_equiv. intros.
  destruct x. auto.
Defined.
Obligation 2.
  unfold Symmetric, HMachine_equiv. intros.
  destruct x. destruct y.
  symmetry; assumption.
Defined.
Obligation 3.
  unfold Transitive, HMachine_equiv. intros.
  destruct x. destruct y. destruct z.
  transitivity s0; auto.
Defined.

Add Parametric Relation {u} (a b : Type) : (@HMachine u a b) (@HMachine_equiv u a b)
  reflexivity proved by  (@Equivalence_Reflexive  _ _ (HMachine_equivalence a b))
  symmetry proved by     (@Equivalence_Symmetric  _ _ (HMachine_equivalence a b))
  transitivity proved by (@Equivalence_Transitive _ _ (HMachine_equivalence a b))
    as parametric_relation_HMachine_eqv.

  Add Parametric Morphism {u} (a b c : Type) : (@hcompose u a b c)
    with signature (HMachine_equiv ==> HMachine_equiv ==> HMachine_equiv)
      as parametric_morphism_hcomp.
    intros. unfold HMachine_equiv, hcompose.
    destruct x. destruct y. destruct x0. destruct y0.
    simpl in *. intros.
    unfold func_eqv. intros.
    extensionality zz. auto.
Defined.

(*
Program Instance HMachine_Category : Category := {
    ob      := Type;
    hom     := @HMachine unit;
    id      := fun X => lift tt (@id Sets X);
    compose := @hcompose unit;
    eqv     := @HMachine_equiv unit
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

CoFixpoint HMachine_run {a : Type} (h : HMachine a a) : stream (a → a) :=
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

Theorem hstream_functor_faithful : forall {a b} (f g : a → b) (seed : b),
  lift f = lift g → f = g.
Proof.
  intros.
  assert (forall x, f x = project seed (lift f) x). auto.
  rewrite H in H0.
  extensionality x.
  rewrite H0. auto.
Qed.
*)

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

CoFixpoint colift {a b} (f : a -> b) : HStream a b := f :<<: colift f.

CoFixpoint cohcompose {a b c}
  (hf : HStream b c) (hg : HStream a b) : HStream a c :=
  match hf with
  | f :<<: fs => match hg with
    | g :<<: gs => (@compose Sets _ _ _ f g) :<<: (cohcompose fs gs)
    end
  end.

Infix ":<<:" := HCons (at level 98, left associativity).

Hypothesis hstream_equality : forall {a b} (x y : HStream a b),
  hstream_eq x y -> x = y.

(*
Program Instance HStream_Category : Category := {
    ob := @ob Sets;
    hom := HStream;
    id := fun X => colift (@id Sets X);
    compose := @cohcompose
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
*)

CoFixpoint HStream_run {a : Type} (h : HStream a a) : stream (a -> a) :=
  match h with
  | f :<<: fs => Cons f (HStream_run fs)
  end.

(*
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
*)

(*
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
*)

Theorem hstream_functor_faithful : forall {a b} (f g : a -> b) (seed : b),
  colift f = colift g -> f = g.
Proof.
  intros.
Abort.
(*   assert (forall x, f x = project seed (colift f) x). auto. *)
(*   rewrite H in H0. *)
(*   extensionality x. *)
(*   rewrite H0. auto. *)
(* Qed. *)
