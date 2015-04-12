Generalizable All Variables.

(* A container takes a set of shapes [S] and a family of types [P] indexed by
   [S]. Using these two, we may construct a box for one such shape [x : S]
   along with a function (unnamed, but let's call it [f]) that, given some
   "index" [i : P x], yields the contained element corresponding to [i], of
   type [a].

   For example, the shape of a list of type [list a] may be described by its
   length [n : nat], along with an accessor of type [Fin n -> a]. Thus:

     S = nat
     P = forall n : S, Fin n
     x : S
     f : P x -> a := fun (i : P x) => nth i <some Vector x a>

   The accessor in this case need not be a closure over [Vector x a], but is
   always isomorphic to it.

   The benefit of this abstraction is that any type representable as a
   container must be strictly positive, since its elements are demonstrably
   finite (its use is contingent on the inhabitants of [S] and [P x]). *)

Record Container `(IndexType : Shape -> Type) (a : Type) := {
    shape  : Shape;
    getter : IndexType shape -> a
}.

Arguments shape  [Shape IndexType a] c.
Arguments getter [Shape IndexType a] c idx.

Require Export Endo.

Program Instance Container_Functor {S : Type} (P : S -> Type) :
  Functor (Container P) := {
  fmap := fun X Y f x =>
    {| shape  := shape x
     ; getter := fun i => f (getter x i)
     |}
}.
Obligation 1. extensionality x; destruct x; reflexivity. Qed.

Record Monoid (a : Type) := {
    mempty  : a;
    mappend : a -> a -> a;

    m_left  : forall x, mappend mempty x = x;
    m_right : forall x, mappend x mempty = x;
    m_assoc : forall x y z, mappend x (mappend y z) = mappend (mappend x y) z
}.

Definition AContainer
  `(IndexType : Shape -> Type)
  (M : Monoid Shape) (MP : forall s : Shape, Monoid (IndexType s)) (a : Type) :=
  Container IndexType a.

Require Export Applicative.

Program Instance AContainer_Functor
  {S : Type} (P : S -> Type) (M : Monoid S) (MP : forall s : S, Monoid (P s)) :
  Functor (AContainer P M MP) := Container_Functor P.

Program Instance AContainer_Applicative
  {S : Type} (P : S -> Type) (M : Monoid S) (MP : forall s : S, Monoid (P s)) :
  Applicative (AContainer P M MP) := {
  pure := fun X x =>
    {| shape  := mempty S M
     ; getter := fun _ => x
     |};
  ap := fun X Y f x =>
    {| shape  := mappend S M (shape f) (shape x)
     ; getter := fun i => getter f i (getter x i)
     |}
}.
Obligation 1. Admitted.
Obligation 2. Admitted.
Obligation 3. Admitted.
Obligation 4. Admitted.
Obligation 5. Admitted.
Obligation 6. Admitted.
Obligation 7. Admitted.

Inductive FreeF {A : Type} (P : A -> Type) (a b : Type) :=
  | Pure : a -> FreeF P a b
  | Free : Container P b -> FreeF P a b.

Inductive FreeT {CM CF : Type} (PM : CM -> Type) (PF : CF -> Type) (a : Type) :=
  runFreeT : Container PM (FreeF PF a (FreeT PM PF a)) -> FreeT PM PF a.

(* The pipes Proxy functor has only two shapes: requesting and responding.
   This is equivalent to [a' + b]. *)
Inductive ProxyFS a' b :=
  | Request : a' -> ProxyFS a' b
  | Respond : b  -> ProxyFS a' b.

(* These two shapes accept accessors of the following types, yielding the
   "contained type" that is the next Proxy in the pipeline. *)
Definition ProxyFP (a' a b' b : Type) (proxy : ProxyFS a' b) :=
  match proxy with
  | Request _ => a
  | Respond _ => b'
  end.

(* The underlying Monad must be represened as a container type so we can know
   that it is always capable of producing a value. This restricts the set of
   monads that can be used with our Proxy to only those that are strictly
   positive functors. *)
Definition Proxy a' a b' b (M : Type) (P : M -> Type) r :=
  FreeT P (ProxyFP a' a b' b) r.

(*
Definition runEffect (x : Proxy Void () () Void m r) : m r :=
  let c := runFreeT x in

runEffect = go . runProxy
  where
    go p = runFreeT p >>= \case
        Free (Request _ f) -> go (f ())
        Free (Respond _ f) -> go (f ())
        Pure r             -> return r

respond :: Monad m => a -> Proxy x' x a' a m a'
respond a = Proxy $ FreeT $ return $ Free $ Respond a (FreeT . return . Pure)
*)

Definition Producer  b := Proxy False unit unit b.
Definition Producer' b m p r := forall x' x, Proxy x' x unit b m p r.
