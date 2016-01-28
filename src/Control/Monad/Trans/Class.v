Require Import Hask.Prelude.
Require Import Hask.Control.Monad.

Generalizable All Variables.

Class MonadTrans (T : (Type -> Type) -> Type -> Type) :=
{ lift : forall (M : Type -> Type) `{Monad M} `{Monad (T M)} A, M A -> T M A
}.

Arguments lift {T _ M _ _ A} _.

Notation "lift/ M" := (@lift M _ _ _) (at level 9).
Notation "lift/ M N" := (@lift (fun X => M (N X)) _ _ _) (at level 9).

Module MonadTransLaws.

Include MonadLaws.

Class MonadTransLaws `{MonadTrans T} :=
{ trans_law_1 :
    forall (M : Type -> Type) `{MonadLaws M} `{MonadLaws (T M)} A,
      lift \o pure/M = (@pure (T M) _ A);
  trans_law_2 :
    forall (M : Type -> Type) `{MonadLaws M} `{MonadLaws (T M)} A
      (f : A -> M A) (m : M A),
        lift (m >>= f) = (@lift _ _ _ _ _ A m) >>= (lift \o f)
}.

Theorem trans_law_1_x : forall (T : (Type -> Type) -> Type -> Type)
  {M : Type -> Type} `{m : MonadLaws M} `{tm : MonadLaws (T M)}
  `{MonadTransLaws T} {A : Type} {x : A},
  lift ((pure/M) x) = (@pure (T M) _ A) x.
Proof.
  intros.
  destruct H2.
  specialize (trans_law_3 M _).
  rewrite <- trans_law_3.
  reflexivity.
  assumption.
  assumption.
Qed.

End MonadTransLaws.