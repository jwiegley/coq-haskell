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
      (f << p) ∘ (g << q) = (@compose Sets _ _ _ f g) << (p ∘ q);

    hyper_law_lift : forall {a b} (f : a → b), fmap' f = f << fmap' f;

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

(*
Program Instance HMachine_Category : Category := {
    ob      := Type;
    hom     := @HMachine unit;
    id      := fun X => lift tt (@id Sets X);
    compose := @hcompose unit
}.
Obligation 1.
  unfold hcompose, lift.
  destruct f. simpl.
Qed.
Obligation 2.
  unfold hcompose, lift.
  destruct f. simpl.
Qed.
Obligation 3.
  unfold hcompose.
  destruct f. destruct g. destruct h.
  simpl.
  apply f_equal2 with pair_assoc.
Defined.

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
Qed.

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

Program Instance HStream_Category : Category := {
    ob := @ob Sets;
    hom := HStream;
    id := fun X => colift (@id Sets X);
    compose := @cohcompose
}.
Obligation 1.
  apply hstream_equality.
  rewrite (frob_eq (cohcompose f (colift (fun x : A => x)))).
  rewrite (frob_eq f).
  simpl. destruct f. simpl.
  revert b f. cofix.
  intros. constructor. destruct f.
  rewrite (frob_eq (cohcompose _ (colift (fun x : A => x)))).
  rewrite (frob_eq f).
  simpl. apply HStream_Category_obligation_1.
Defined.
Obligation 2.
  apply hstream_equality.
  rewrite (frob_eq (cohcompose (colift (fun x : B => x)) f)).
  rewrite (frob_eq f).
  simpl. destruct f. simpl.
  revert b f. cofix.
  intros. constructor. destruct f.
  rewrite (frob_eq (cohcompose (colift (fun x : B => x)) _)).
  rewrite (frob_eq f).
  simpl. apply HStream_Category_obligation_2.
Defined.
Obligation 3.
  apply hstream_equality.
  rewrite (frob_eq (cohcompose f (cohcompose g h))).
  rewrite (frob_eq (cohcompose (cohcompose f g) h)).
  simpl. destruct f. destruct g. destruct h. simpl.
  revert d f c g b h. cofix.
  intros. constructor.
  destruct f. destruct g. destruct h.
  rewrite (frob_eq (cohcompose _ (cohcompose _ _))).
  rewrite (frob_eq (cohcompose (cohcompose _ _) _)).
  simpl. apply HStream_Category_obligation_3.
Defined.

CoFixpoint HStream_run {a : Type} (h : HStream a a) : stream a.
Admitted.
 (* := *)
 (*  match h with *)
 (*  | f :<<: fs => Cons f (HStream_run fs) *)
 (*  end. *)

Program Instance HStream_Functor : Sets ⟶ HStream_Category := {
    fobj := fun x => x;
    fmap := @colift
}.
Obligation 2.
  apply hstream_equality.
  rewrite (frob_eq (cohcompose (colift f) (colift g))).
  rewrite (frob_eq (colift (λ x : X, f (g x)))).
  simpl. destruct (colift f). destruct (colift g).
  destruct h. destruct h0.
  revert z z0 h y y0 h0. cofix.
  intros. constructor.
  destruct h. destruct h0.
  specialize (HStream_Functor_obligation_2 z0 z1 h y0 y1 h0).
  rewrite (frob_eq (cohcompose _ _)).
  rewrite (frob_eq (colift _)).
  simpl. (* apply HStream_Functor_obligation_2. *)
Admitted.

Program Instance HStream_Hyper : Hyperfunction HStream_Functor := {
    run := fun X => @HStream_run X
}.
Obligation 4.
  unfold HStream_Hyper_obligation_1.
  apply stream_equality.
  rewrite (sfrob_eq (HStream_run (cohcompose p q))).
  rewrite (sfrob_eq (stream_map f (HStream_run (cohcompose q p)))).
  simpl. destruct p. destruct q.
  revert b0 a0 p q.
  cofix. intros.
  (* jww (2014-08-24): Need to define HStream_run. *)
Admitted.

CoFixpoint repeat_value {a} (x : a) : stream a :=
  Cons x (repeat_value x).

Theorem hstream_functor_faithful : forall {a b} (f g : a -> b),
  colift f = colift g -> f = g.
Proof.
  intros.
  assert (forall x, repeat_value (f x) = project (colift f) x).
    admit.
  rewrite H in H0.
  extensionality x.
Admitted.
