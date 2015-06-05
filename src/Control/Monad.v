Require Import Hask.Prelude.
Require Import Hask.Data.List.
Require Export Hask.Control.Applicative.

Generalizable All Variables.

Class Monad (m : Type -> Type) := {
  is_applicative :> Applicative m;

  join : forall {a : Type}, m (m a) -> m a
}.

Arguments join {m _ _} _.

Definition bind `{Monad m} {X Y : Type} (f : (X -> m Y)) : m X -> m Y :=
  join \o fmap f.

Notation "m >>= f" := (bind f m) (at level 25, left associativity).
Notation "a >> b" := (a >>= fun _ => b) (at level 25, left associativity).

Definition kleisli_compose `{Monad m} `(f : b -> m c) `(g : a -> m b) :
  a -> m c := fun x => g x >>= f.

Notation "f >=> g" := (kleisli_compose g f) (at level 25, left associativity).
Notation "f >=[ m ]=> g" :=
  (@kleisli_compose _ m _ _ g _ f) (at level 25, left associativity).

Notation "X <-- A ;; B" := (A >>= (fun X => B))
  (right associativity, at level 92, A at next level, only parsing).

Notation "A ;; B" := (_ <-- A ;; B) (at level 92, right associativity,
                                     only parsing).

Fixpoint mapM `{Applicative m} {A B} (f : A -> m B) (l : seq A) :
  m (seq B) :=
  match l with
  | nil => pure nil
  | cons x xs => liftA2 (@cons _) (f x) (mapM f xs)
  end.

Definition forM `{Applicative m} {A B} (l : seq A) (f : A -> m B) :
  m (seq B) := mapM f l.

Fixpoint mapM_ `{Monad m} {A B} (f : A -> m B) (l : seq A) : m unit :=
  match l with
  | nil => pure tt
  | cons x xs => f x >> mapM_ f xs
  end.

Definition forM_ `{Monad m} {A B} (l : seq A) (f : A -> m B) : m unit :=
  mapM_ f l.

Definition foldM `{Monad m} {A : Type} {B : Type}
  (f : A -> B -> m A) (s : A) (l : seq B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => pure z
        | cons y ys => f z y >>= go ys
      end in
  go l s.

Definition forFoldM `{Monad m} {A : Type} {B : Type}
  (s : A) (l : seq B) (f : A -> B -> m A) : m A := foldM f s l.

Definition foldrM `{Monad m} {A : Type} {B : Type}
  (f : B -> A -> m A) (s : A) (l : seq B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => pure z
        | cons y ys => go ys z >>= f y
      end in
  go l s.

Definition forFoldrM `{Monad m} {A : Type} {B : Type}
  (s : A) (l : seq B) (f : B -> A -> m A) : m A := foldrM f s l.

Definition concatMapM `{Applicative m} {A B}
  (f : A -> m (seq B)) (l : seq A) : m (seq B) :=
  fmap (concat) (mapM f l).

Fixpoint insertM `{Monad m} {a} (P : a -> a -> m bool)
  (z : a) (l : list a) : m (list a) :=
  if l is x :: xs
  then
    b <-- P x z ;;
    if b
    then cons x <$> insertM P z xs
    else pure (z :: x :: xs)
  else pure [:: z].
Arguments insertM {m H a} P z l : simpl never.

Module MonadLaws.

Include ApplicativeLaws.

Class MonadLaws (m : Type -> Type) `{Monad m} := {
  has_applicative_laws :> ApplicativeLaws m;

  join_fmap_join : forall a : Type, join \o fmap (@join m _ a) =1 join \o join;
  join_fmap_pure : forall a : Type, join \o fmap (pure (a:=a)) =1 id;
  join_pure      : forall a : Type, join \o pure =1 @id (m a);
  join_fmap_fmap : forall (a b : Type) (f : a -> b),
    join \o fmap (fmap f) =1 fmap f \o join
}.

Corollary join_fmap_join_x `{MonadLaws m} : forall a x,
  join (fmap (join (a:=a)) x) = join (join x).
Proof. exact: join_fmap_join. Qed.

Corollary join_fmap_pure_x `{MonadLaws m} : forall a x,
  join (fmap (pure (a:=a)) x) = x.
Proof. exact: join_fmap_pure. Qed.

Corollary join_pure_x `{MonadLaws m} : forall a x,
  join (pure x) = @id (m a) x.
Proof. exact: join_pure. Qed.

Corollary join_fmap_fmap_x `{MonadLaws m} : forall (a b : Type) (f : a -> b) x,
  join (fmap (fmap f) x) = fmap f (join x).
Proof. exact: join_fmap_fmap. Qed.

End MonadLaws.
