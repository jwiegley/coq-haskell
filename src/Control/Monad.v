Require Export Hask.Control.Applicative.

Generalizable All Variables.

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

Fixpoint mapM_ `{Monad m} {A B} (f : A -> m B) (l : list A) : m unit :=
  match l with
  | nil => pure tt
  | cons x xs => f x >> mapM_ f xs
  end.

Definition forM_ `{Monad m} {A B} (l : list A) (f : A -> m B) : m unit :=
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
  fmap flatten (mapM f l).

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

Instance Compose_Monad `{Monad_Distributes M N}
  : Monad (M \o N) :=
{ is_applicative := Compose_Applicative M N
; join := fun A => join[M] \o fmap[M] (prod M N A)
}.


Instance Impl_Monad {A} : Monad (fun B => A -> B) := {
  join := fun A run => fun xs => run xs xs
}.

Program Instance Impl_Monad_Distributes `{Monad N} :
  @Monad_Distributes (fun B => A -> B) Impl_Monad N is_applicative.
Obligation 1.
  exact (X >>= fun f => f X0).
Defined.

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
Class Monad_DistributesLaws `{Monad_Distributes M N} :=
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

Program Instance Compose_MonadLaws `{Monad_DistributesLaws M N} :
  MonadLaws (M \o N).
Obligation 1. (* monad_law_1 *)
  intros.
  rewrite <- comp_assoc with (f := join[M]).
  rewrite <- comp_assoc with (f := join[M]).
  rewrite comp_assoc with (f := fmap[M] (prod M N a)).
  rewrite <- join_fmap_fmap.
  rewrite <- comp_assoc.
  rewrite comp_assoc with (f := join[M]).
  rewrite comp_assoc with (f := join[M]).
  rewrite <- join_fmap_join.
  repeat (rewrite <- comp_assoc).
  repeat (rewrite fmap_comp).
  repeat (rewrite comp_assoc).
  rewrite <- prod_fmap_join_fmap_prod.
  reflexivity.
Qed.
Obligation 2. (* monad_law_2 *)
  intros.
  rewrite <- join_fmap_pure.
  repeat (rewrite <- comp_assoc).
  repeat (rewrite fmap_comp).
  repeat f_equal.
  pose proof (@prod_fmap_pure M _ N _ _ _ a).
  simpl in H3.
  rewrite H3.
  reflexivity.
Qed.
Obligation 3. (* monad_law_3 *)
  intros.
  rewrite <- prod_pure.
  rewrite <- comp_id_left.
  rewrite <- (@join_pure M _ _ (N a)).
  rewrite <- comp_assoc.
  rewrite <- comp_assoc.
  f_equal.
  rewrite comp_assoc.
  rewrite comp_assoc.
  f_equal.
  rewrite <- fmap_pure.
  reflexivity.
Qed.
Obligation 4. (* monad_law_4 *)
  intros.
  unfold comp at 2.
  rewrite comp_assoc.
  rewrite <- join_fmap_fmap.
  rewrite <- comp_assoc.
  rewrite fmap_comp.
  pose proof (@prod_fmap_fmap M _ N _ _ _ a).
  simpl in H3.
  rewrite <- H3.
  rewrite <- fmap_comp.
  reflexivity.
Qed.

Program Instance Impl_MonadLaws : MonadLaws (fun B => A -> B).

Require Import FunctionalExtensionality.

Program Instance Impl_Monad_DistributesLaws `{MonadLaws N} :
  @Monad_DistributesLaws (fun B => A -> B) Impl_Monad N is_applicative
                         Impl_Monad_Distributes.
Obligation 1.
  unfold Impl_Monad_Distributes_obligation_1, comp, bind, id.
  extensionality x.
  extensionality x0.
  simpl.
  rewrite <- join_fmap_fmap_x, !fmap_comp_x.
  reflexivity.
Qed.
Obligation 2.
  unfold Impl_Monad_Distributes_obligation_1, comp, bind, id.
  extensionality x.
  extensionality x0.
  simpl.
  rewrite fmap_pure_x, join_pure_x.
  reflexivity.
Qed.
Obligation 3.
  unfold Impl_Monad_Distributes_obligation_1, comp, bind, id.
  extensionality x.
  extensionality x0.
  simpl.
  rewrite fmap_comp_x, join_fmap_pure_x.
  reflexivity.
Qed.
Obligation 4.
  unfold Impl_Monad_Distributes_obligation_1, comp, bind, id.
  extensionality x.
  extensionality x0.
  simpl.
  rewrite <- join_fmap_fmap_x, <- join_fmap_join_x, !fmap_comp_x.
  reflexivity.
Qed.

End MonadLaws.
