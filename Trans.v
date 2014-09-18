Require Export Monad.

Class MonadTrans (T : (Type -> Type) -> Type -> Type)
  {M : Type -> Type} `{Monad M} `{Monad (T M)} :=
{ lift : forall {A}, M A -> T M A

; trans_law_1 : forall {A}, lift ∘ pure/M = (@pure (T M) _ A)
; trans_law_2 : forall {A} (f : A -> M A) (m : M A),
    lift (m >>= f) = (@lift A m) >>= (lift ∘ f)
}.

Notation "lift/ M" := (@lift M _ _ _) (at level 28).
Notation "lift/ M N" := (@lift (fun X => M (N X)) _ _ _) (at level 26).

Theorem trans_law_1_x
  : forall (T : (Type -> Type) -> Type -> Type) {M : Type -> Type}
    `{m : Monad M} `{tm : Monad (T M)} `{@MonadTrans T M m tm}
    {A : Type} {x : A},
  lift ((pure/M) x) = (@pure (T M) _ A) x.
Proof.
  intros.
  assert ((lift/T) _ _ ((pure/M) x) = ((lift/T) _ _ ∘ (pure/M)) x).
    unfold compose. reflexivity.
  rewrite H0.
  rewrite trans_law_1.
  reflexivity.
Qed.
