Require Export Hask.Control.Applicative.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Monad (m : Type -> Type) := {
  is_applicative :> Applicative m;

  join : forall {a : Type}, m (m a) -> m a
}.

Arguments join {m _ _} _.

Definition bind `{Monad m} {X Y : Type} (f : (X -> m Y)) : m X -> m Y :=
  join \o fmap f.

Definition return_ `{Monad m} {a} : a -> m a := pure.

Delimit Scope monad_scope with monad.

Notation "join[ M ]" := (@join M _ _) (at level 9) : monad_scope.
Notation "join[ M N ]" := (@join (M \o N) _ _) (at level 9) : monad_scope.

Notation "m >>= f" := (bind f m) (at level 42, right associativity) : monad_scope.
Notation "a >> b" := (a >>= fun _ => b)%monad (at level 81, right associativity) : monad_scope.

Bind Scope monad_scope with Monad.

Definition kleisli_compose `{Monad m} `(f : a -> m b) `(g : b -> m c) :
  a -> m c := fun x => (f x >>= g)%monad.

Infix ">=>" := kleisli_compose (at level 42, right associativity) : monad_scope.
Notation "f <=< g" :=
  (kleisli_compose g f) (at level 42, right associativity) : monad_scope.

Notation "f >=[ m ]=> g" :=
  (@kleisli_compose _ m _ _ f _ g) (at level 42, right associativity) : monad_scope.
Notation "f <=[ m ]=< g" :=
  (@kleisli_compose _ m _ _ g _ f) (at level 42, right associativity) : monad_scope.

Notation "X <- A ; B" := (A >>= (fun X => B))%monad
  (at level 81, right associativity, only parsing) : monad_scope.

Notation "A ;; B" := (A >>= (fun _ => B))%monad
  (at level 81, right associativity, only parsing) : monad_scope.

Open Scope monad_scope.

Definition when `{Monad m} `(b : bool) (x : m unit) : m unit :=
  if b then x else return_ tt.

Definition unless `{Monad m} `(b : bool) (x : m unit) : m unit :=
  if negb b then x else return_ tt.

Fixpoint mapM `{Applicative m} {A B} (f : A -> m B) (l : list A) :
  m (list B) :=
  match l with
  | nil => pure nil
  | cons x xs => liftA2 (@cons _) (f x) (mapM f xs)
  end.

Definition forM `{Applicative m} {A B} (l : list A) (f : A -> m B) :
  m (list B) := mapM f l.

Fixpoint mapM_ `{Applicative m} {A B} (f : A -> m B) (l : list A) : m unit :=
  match l with
  | nil => pure tt
  | cons x xs => liftA2 (const id) (f x) (mapM_ f xs)
  end.

Definition forM_ `{Applicative m} {A B} (l : list A) (f : A -> m B) : m unit :=
  mapM_ f l.

Definition foldM `{Monad m} {A : Type} {B : Type}
  (f : A -> B -> m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => pure z
        | cons y ys => f z y >>= go ys
      end in
  go l s.

Definition forFoldM `{Monad m} {A : Type} {B : Type}
  (s : A) (l : list B) (f : A -> B -> m A) : m A := foldM f s l.

Definition foldrM `{Monad m} {A : Type} {B : Type}
  (f : B -> A -> m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => pure z
        | cons y ys => go ys z >>= f y
      end in
  go l s.

Definition forFoldrM `{Monad m} {A : Type} {B : Type}
  (s : A) (l : list B) (f : B -> A -> m A) : m A := foldrM f s l.

Fixpoint flatten `(xs : list (list A)) : list A :=
  match xs with
  | nil => nil
  | cons x xs' => app x (flatten xs')
  end.

Definition concatMapM `{Applicative m} {A B}
  (f : A -> m (list B)) (l : list A) : m (list B) :=
  let xs : m (list (list B)) := mapM f l in
  fmap flatten xs.

Fixpoint replicateM_ `{Monad m} (n : nat) (x : m unit) : m unit :=
  match n with
  | O => pure tt
  | S n' => x >> replicateM_ n' x
  end.

Fixpoint insertM `{Monad m} {a} (P : a -> a -> m bool)
  (z : a) (l : list a) : m (list a) :=
  match l with
  | nil => pure (cons z nil)
  | cons x xs =>
    b <- P x z ;
    if (b : bool)
    then cons x <$> insertM P z xs
    else pure (cons z (cons x xs))
  end.
Arguments insertM {m H a} P z l : simpl never.

Class Monad_Distributes `{Monad M} `{Applicative N} :=
{ prod : forall A, N (M (N A)) -> M (N A)
}.

Arguments prod M {_} N {_ Monad_Distributes} A _.

Module MonadLaws.

Include ApplicativeLaws.

Class MonadLaws (m : Type -> Type) `{Monad m} := {
  has_applicative_laws :> ApplicativeLaws m;

  join_fmap_join : forall a, join \o fmap (@join m _ a) = join \o join;
  join_fmap_pure : forall a, join \o fmap (pure (a:=a)) = id;
  join_pure      : forall a, join \o pure = @id (m a);
  join_fmap_fmap : forall a b (f : a -> b),
    join \o fmap (fmap f) = fmap f \o join
}.

Corollary join_fmap_join_x `{MonadLaws m} : forall a x,
  join (fmap (join (a:=a)) x) = join (join x).
Proof.
  intros.
  replace (join[m] (join[m] x)) with ((join[m] \o join[m]) x).
    rewrite <- join_fmap_join.
    reflexivity.
  reflexivity.
Qed.

Corollary join_fmap_pure_x `{MonadLaws m} : forall a x,
  join (fmap (pure (a:=a)) x) = x.
Proof.
  intros.
  replace x with (id x) at 2; auto.
  rewrite <- join_fmap_pure.
  reflexivity.
Qed.

Corollary join_pure_x `{MonadLaws m} : forall a x,
  join (pure x) = @id (m a) x.
Proof.
  intros.
  rewrite <- join_pure.
  reflexivity.
Qed.

Corollary join_fmap_fmap_x `{MonadLaws m} : forall (a b : Type) (f : a -> b) x,
  join (fmap (fmap f) x) = fmap f (join x).
Proof.
  intros.
  replace (fmap[m] f (join[m] x)) with ((fmap[m] f \o join[m]) x).
    rewrite <- join_fmap_fmap.
    reflexivity.
  reflexivity.
Qed.

(* These proofs are due to Mark P. Jones and Luc Duponcheel in their article
   "Composing monads", Research Report YALEU/DCS/RR-1004, December 1993.

   Given any Monad M, and any Premonad N (i.e., having pure), and further given
   an operation [prod] and its accompanying four laws, it can be shown that M
   N is closed under composition.
*)
Class Monad_DistributesLaws `{Applicative (M \o N)} `{Monad_Distributes M N} :=
{
  m_monad_laws :> MonadLaws M;
  n_applicative_laws :> ApplicativeLaws N;

  prod_fmap_fmap : forall A B (f : A -> B),
    prod M N B \o fmap[N] (fmap[M \o N] f) = fmap[M \o N] f \o prod M N A;
  prod_pure : forall A, prod M N A \o pure[N] = @id (M (N A));
  prod_fmap_pure : forall A, prod M N A \o fmap[N] (pure[M \o N]) = pure[M];
  prod_fmap_join_fmap_prod : forall A,
    prod M N A \o fmap[N] (join[M] \o fmap[M] (prod M N A))
      = join[M] \o fmap[M] (prod M N A) \o prod M N (M (N A))
}.

End MonadLaws.
