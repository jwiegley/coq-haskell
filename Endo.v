Require Export Basics.

Generalizable All Variables.

(* Even though we have the Category class in Category.v, the Functors
   and Monads I'm interested in reasoning about are all endofunctors on
   Coq, so there is no reason to carry around that extra machinery. *)

Class Functor (F : Type -> Type) :=
{ fobj := F
; fmap : forall {X Y}, (X -> Y) -> F X -> F Y

; fun_identity : forall {X}, fmap (@id X) = id
; fun_composition : forall {X Y Z} (f : Y -> Z) (g : X -> Y),
    fmap f ∘ fmap g = fmap (f ∘ g)
}.

Arguments fmap            [F] [Functor] [X] [Y] f g.
Arguments fun_identity    [F] [Functor] [X].
Arguments fun_composition [F] [Functor] [X] [Y] [Z] f g.

Notation "f <$> g" := (fmap f g) (at level 28, left associativity).

Notation "fmap[ M ]  f" := (@fmap M _ _ _ f) (at level 28).
Notation "fmap[ M N ]  f" := (@fmap (fun X => M (N X)) _ _ _ f) (at level 26).
Notation "fmap[ M N O ]  f" := (@fmap (fun X => M (N (O X))) _ _ _ f) (at level 24).

Coercion fobj : Functor >-> Funclass.

Lemma fun_irrelevance `(F : Functor)
  : ∀ (f g : ∀ {X Y}, (X -> Y) → (F X -> F Y))
      i i' c c',
  @f = @g →
  {| fmap := @f
   ; fun_identity    := i
   ; fun_composition := c |} =
  {| fmap := @g
   ; fun_identity    := i'
   ; fun_composition := c' |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.

Section Functors.

  Variable F : Type -> Type.
  Context `{Functor F}.

  Theorem fun_identity_x : forall {X} (x : F X), fmap id x = id x.
  Proof.
    intros.
    rewrite fun_identity.
    reflexivity.
  Qed.

  Theorem fun_composition_x
    : forall {X Y Z} (f : Y -> Z) (g : X -> Y) (x : F X),
    f <$> (g <$> x) = (f ∘ g) <$> x.
  Proof.
    intros.
    rewrite <- fun_composition.
    reflexivity.
  Qed.

End Functors.

(* Functions are trivial functors. *)

(*
Program Instance Hom_Functor {A} : Functor (fun X => A -> X) :=
{ fmap := fun X Y f g => f ∘ g
}.
*)

Class Natural `(Functor F) `(Functor G) := {
    transport  : ∀ {X}, F X -> G X;
    naturality : ∀ {X Y} (f : X -> Y),
      fmap f ∘ transport = transport ∘ fmap f
}.

Notation "transport/ N" := (@transport _ _ _ _ N _) (at level 24).
Notation "F ⟾ G" := (Natural F G) (at level 90, right associativity).

Lemma nat_irrelevance `(F : Functor) `(G : Functor)
  : ∀ (f g : ∀ {X}, F X -> G X) n n',
  @f = @g ->
  {| transport := @f; naturality := n |} =
  {| transport := @g; naturality := n' |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
Qed.

Class Full `(F : Functor) := {
    full_prop : ∀ {X Y} (g : F X -> F Y) (f : X -> Y), g = fmap f
}.

Class Faithful `(F : Functor) := {
    faithful_prop : ∀ {X Y} (f1 f2 : X -> Y), fmap f1 = fmap f2 -> f1 = f2
}.

Class FullyFaithful `(F : Functor) := {
    is_full :> Full F;
    is_faithful :> Faithful F;

    unfmap : ∀ {X Y}, (F X -> F Y) -> (X -> Y)
}.

Program Instance Hom (A : Type) : Functor (fun X => A -> X) := {
    fmap := @compose _
}.

Definition hom_irrelevance : forall {A X}, (A -> X) -> Hom A X.
Proof. auto. Defined.

Definition hom_irrelevance_r : forall {A} X, Hom A X -> (A -> X).
Proof. auto. Defined.

(* Open Scope nat_scope. *)

(* Theorem distributive : forall n m o : nat, *)
(*   (n + m) * (n + o) = n * n + m * n + m * o + n * o. *)
(* Proof. *)
(*   intros. induction n; simpl. *)
(*     omega. *)
(*   rewrite Mult.mult_succ_r. *)
(*   rewrite IHn. *)
(*   repeat rewrite <- Plus.plus_assoc. *)
(*   rewrite (Plus.plus_comm o). *)
(*   rewrite (Plus.plus_comm o). *)
(*   rewrite Mult.mult_succ_r. *)
(*   rewrite Mult.mult_succ_r. *)
(*   omega. *)
(* Qed. *)

Program Instance Hom_Full (A : Type) : Full (Hom A).
Obligation 1.
Admitted.

Program Instance Hom_Faithful (A : Type) : Faithful (Hom A).
Obligation 1.
Admitted.

Program Instance Hom_FullyFaithful (A : Type) : FullyFaithful (Hom A).
Obligation 1.
  pose (@full_prop _ (Hom A) _ X Y X0).
  pose (@faithful_prop _ (Hom A) _ X Y).
  apply (X0 (const X1)).
Admitted.

Program Instance option_Functor : Functor option := {
    fmap := fun _ _ f x => match x with
      | None => None
      | Some x => Some (f x)
      end
}.
Obligation 1. extensionality x. destruct x; auto. Qed.
Obligation 2. extensionality x. destruct x; auto. Qed.

Program Instance list_Functor : Functor list := {
    fmap := List.map
}.
Obligation 1.
  extensionality l.
  induction l; auto.
  simpl. rewrite IHl.
  reflexivity.
Qed.
Obligation 2.
  extensionality l.
  induction l; auto.
  simpl. rewrite <- IHl.
  reflexivity.
Qed.
