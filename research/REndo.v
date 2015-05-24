Require Export Basics.

Generalizable All Variables.

(* Even though we have the Category class in Category.v, the Functors
   and Monads I'm interested in reasoning about are all endofunctors on
   Coq, so there is no reason to carry around that extra machinery. *)

Class RFunctor {a : Type} (F : a -> a -> relation a -> Type -> Type) :=
{ robj := F
; rmap : forall {I O P X Y}, (X -> Y) -> F I O P X -> F I O P Y

; rfun_identity : forall {I O P X}, @rmap I O P _ _ (@id X) = id
; rfun_composition : forall {I O P X Y Z} (f : Y -> Z) (g : X -> Y),
    rmap f ∘ rmap g = @rmap I O P _ _ (f ∘ g)
}.

Arguments rmap             {a F RFunctor I O P X Y} f g.
Arguments rfun_identity    {a F RFunctor I O P X}.
Arguments rfun_composition {a F RFunctor I O P X Y Z} f g.

Notation "f <$$> g" := (rmap f g) (at level 28, left associativity).

Notation "rmap[ M ]  f" := (@rmap M _ _ _ f) (at level 28).
Notation "rmap[ M N ]  f" := (@rmap (fun X => M (N X)) _ _ _ f) (at level 26).
Notation "rmap[ M N O ]  f" := (@rmap (fun X => M (N (O X))) _ _ _ f) (at level 24).

Coercion robj : RFunctor >-> Funclass.

Lemma rfun_irrelevance `(F : RFunctor)
  : ∀ (f g : ∀ {I O P X Y}, (X -> Y) → (F I O P X -> F I O P Y))
      i i' c c',
  @f = @g →
  {| rmap := @f
   ; rfun_identity    := i
   ; rfun_composition := c |} =
  {| rmap := @g
   ; rfun_identity    := i'
   ; rfun_composition := c' |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.

Section RFunctors.

  Variable a : Type.
  Variable F : a -> a -> relation a -> Type -> Type.
  Context `{RFunctor _ F}.

  Theorem rfun_identity_x : forall {I O P X} (x : F I O P X), rmap id x = id x.
  Proof.
    intros.
    rewrite rfun_identity.
    reflexivity.
  Qed.

  Theorem rfun_composition_x
    : forall {I O P X Y Z} (f : Y -> Z) (g : X -> Y) (x : F I O P X),
    f <$$> (g <$$> x) = (f ∘ g) <$$> x.
  Proof.
    intros.
    rewrite <- rfun_composition.
    reflexivity.
  Qed.

End RFunctors.
