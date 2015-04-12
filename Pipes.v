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

(*
Record Monoid (a : Type) := {
    mempty  : a;
    mappend : a -> a -> a;

    m_left  : forall x, mappend mempty x = x;
    m_right : forall x, mappend x mempty = x;
    m_assoc : forall x y z, mappend x (mappend y z) = mappend (mappend x y) z
}.

Definition AContainer {S : Type} (P : S -> Type)
  (D : forall a, a -> Container P a)
  (F : forall a b,
         Container P (a -> b) -> Container P a -> Container P b) := Container P.
*)

Require Export Applicative.

(*
Program Instance AContainer_Functor
  {S : Type} (P : S -> Type) (D : forall a, a -> Container P a)
  (F : forall a b,
         Container P (a -> b) -> Container P a -> Container P b) :
  Functor (AContainer P D F) := Container_Functor P.

Program Instance AContainer_Applicative
  {S : Type} (P : S -> Type) (D : forall a, a -> Container P a)
  (F : forall a b,
         Container P (a -> b) -> Container P a -> Container P b) :
  Applicative (AContainer P D F) := {
  pure := fun X x => D _ x;
  ap := fun X Y f x => F _ _ f x
}.
Obligation 1.
  extensionality x.
  unfold id.
  destruct x; simpl in *.
  clear -m_left0.
  admit.
Admitted.
Obligation 2. Admitted.
Obligation 3. Admitted.
Obligation 4. Admitted.
Obligation 5. Admitted.
*)

Require Export Monad.

(*
Program Instance AContainer_Monad
  {S : Type} (P : S -> Type) (M : Monoid S)
  (MP1 : forall s1 s2 : S, P (mappend S M s1 s2) -> P s1)
  (MP2 : forall s1 s2 : S, P (mappend S M s1 s2) -> P s2) :
  Monad (AContainer P M MP1 MP2) := {
  join := fun _ x =>
    {| shape  := mappend S M (shape f) (shape x)
     ; getter := fun i => getter f (MP1 _ _ i) (getter x (MP2 _ _ i))
     |}
}.
*)

Inductive FreeF `(P : A -> Type) (a b : Type) :=
  | Pure : a -> FreeF P a b
  | Free : Container P b -> FreeF P a b.

Inductive FreeT
  `(PM : CM -> Type) `{Monad (Container PM)}
  `(PF : CF -> Type) (a : Type) :=
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
Definition Proxy a' a b' b `(m : A -> Type)
  `{Monad (Container m)} r := FreeT m (ProxyFP a' a b' b) r.

Fixpoint runEffect (n : nat) `(dflt : r)
  `{m : A -> Type} {H : Monad (Container m)}
  `(x : Proxy False unit unit False m r) {struct n} : Container m r :=
  match n with
  | S n =>
      match x with
      | runFreeT v =>
          y <- v ;
          match y return Container m r with
          | Free {| shape := Request _; getter := f |} =>
              runEffect n dflt (f tt)
          | Free {| shape := Respond _; getter := f |} =>
              runEffect n dflt (f tt)
          | Pure r => pure r
          end
      end
  | Z => pure dflt
  end.

(*
Program Definition respond `{m : A -> Type} `{Monad (Container m)}
  {x' x a' a} (z : a) : Proxy x' x a' a m a' :=
  runFreeT _ _ _ $ pure $
    Free _ _ _ {| shape  := Respond a
                  ; getter := runFreeT _ _ _ ∘ pure ∘ Pure _ _ _ |}.
*)

(* Definition Producer  b := Proxy False unit unit b. *)
(* Definition Producer' b m r := forall x' x, Proxy x' x unit b m r. *)
