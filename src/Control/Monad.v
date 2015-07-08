Require Import Hask.Ssr.
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

Definition return_ `{Monad m} {a} : a -> m a := pure.

Notation "join/ M" := (@join M _ _) (at level 28).
Notation "join/ M N" := (@join (M \o N) _ _) (at level 26).

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

Definition when `{Monad m} `(b : bool) (x : m unit) : m unit :=
  if b then x else return_ tt.

Definition unless `{Monad m} `(b : bool) (x : m unit) : m unit :=
  if ~~ b then x else return_ tt.

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

Fixpoint replicateM_ `{Monad m} (n : nat) (x : m unit) : m unit :=
  if n isn't S n' then pure tt else
  x >> replicateM_ n' x.

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

Class Monad_Distributes `{Monad M} `{Applicative N} :=
{ prod : forall A, N (M (N A)) -> M (N A)
}.

Arguments prod M {_} N {_ Monad_Distributes} A _.

Instance Compose_Monad `{Monad M} `{Applicative N} `{Monad_Distributes M N}
  : Monad (M \o N) :=
{ is_applicative := Compose_Applicative M N
; join := fun A => join/M \o fmap[M] (prod M N A)
}.

Module MonadLaws.

Include ApplicativeLaws.

Class MonadLaws (m : Type -> Type) `{Monad m} := {
  has_applicative_laws :> ApplicativeLaws m;

  join_fmap_join : forall a, join \o fmap (@join m _ a) =1 join \o join;
  join_fmap_pure : forall a, join \o fmap (pure (a:=a)) =1 id;
  join_pure      : forall a, join \o pure =1 @id (m a);
  join_fmap_fmap : forall a b (f : a -> b),
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

(* These proofs are due to Mark P. Jones and Luc Duponcheel in their article
   "Composing monads", Research Report YALEU/DCS/RR-1004, December 1993.

   Given any Monad M, and any Premonad N (i.e., having pure), and further given
   an operation [prod] and its accompanying four laws, it can be shown that M
   N is closed under composition.
*)
Class Monad_DistributesLaws (M N : Type -> Type)
  `{MonadLaws M} `{ApplicativeLaws N} `{Monad_Distributes M N} :=
{
  m_monad_laws :> MonadLaws M;
  n_applicative_laws :> ApplicativeLaws N;

  prod_law_1 : forall A B (f : A -> B),
    prod M N B \o fmap[N] (fmap[M \o N] f) = fmap[M \o N] f \o prod M N A;
  prod_law_2 : forall A, prod M N A \o pure/N = @id (M (N A));
  prod_law_3 : forall A, prod M N A \o fmap[N] (pure/(M \o N)) = pure/M;
  prod_law_4 : forall A,
    prod M N A \o fmap[N] (join/M \o fmap[M] (prod M N A))
      = join/M \o fmap[M] (prod M N A) \o prod M N (M (N A))
}.

(* jww (2015-06-17): Need to port to ssreflect
Program Instance MonadLaws_Compose (M : Type -> Type) (N : Type -> Type)
  `{Monad_DistributesLaws M N} : MonadLaws (M \o N).
Obligation 1. (* monad_law_1 *)
  intros.
  rewrite <- comp_assoc with (f := join/M).
  rewrite <- comp_assoc with (f := join/M).
  rewrite comp_assoc with (f := fmap[M] (@prod M N _ _ _ X)).
  rewrite <- monad_law_4.
  rewrite <- comp_assoc.
  rewrite comp_assoc with (f := join/M).
  rewrite comp_assoc with (f := join/M).
  rewrite <- monad_law_1.
  repeat (rewrite <- comp_assoc).
  repeat (rewrite fun_composition).
  repeat (rewrite comp_assoc).
  rewrite <- prod_law_4.
  repeat (rewrite <- fun_composition).
  unfold compose_fmap. reflexivity.
Obligation 2. (* monad_law_2 *)
  intros.
  rewrite <- monad_law_2.
  rewrite <- prod_law_3. simpl.
  repeat (rewrite <- comp_assoc).
  repeat (rewrite <- fun_composition).
  unfold compose_fmap. reflexivity.
Obligation 3. (* monad_law_3 *)
  intros.
  rewrite <- prod_law_2.
  rewrite <- comp_id_left.
  rewrite <- (@monad_law_3 M _ (N X)).
  rewrite <- comp_assoc.
  rewrite <- comp_assoc.
  rewrite app_fmap_compose. simpl.
  rewrite <- fun_composition.
  rewrite <- comp_assoc.
  unfold compose_pure.
  rewrite <- app_fmap_compose.
  reflexivity.
Obligation 4. (* monad_law_4 *)
  intros. simpl.
  unfold compose_fmap.
  unfold compose at 3.
  unfold compose at 3.
  unfold compose at 4.
  rewrite comp_assoc at 1.
  rewrite <- monad_law_4.
  repeat (rewrite <- comp_assoc).
  rewrite fun_composition.
  rewrite fun_composition.
  pose proof (@prod_law_1 M N _ _ _ X).
  simpl in H4.
  unfold compose_fmap in H4.
  unfold compose in H4 at 2.
  unfold compose in H4 at 3.
  rewrite <- H4.
  reflexivity.
Defined.
*)

End MonadLaws.
