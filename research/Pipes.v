Generalizable All Variables.

Inductive FreeF `(P : A -> Type) (a b : Type) :=
  | Pure : a -> FreeF P a b
  | Free : Container P b -> FreeF P a b.

Arguments Pure {A P a b} _.
Arguments Free {A P a b} _.

Inductive FreeT `(PM : CM -> Type) `{Monad (Container PM)}
  `(PF : CF -> Type) (a : Type) :=
  runFreeT : Container PM (FreeF PF a (FreeT PM PF a)) -> FreeT PM PF a.

Arguments runFreeT {CM PM _ CF PF a} _.

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
Definition Proxy a' a b' b `(m : A -> Type) `{Monad (Container m)} r :=
  FreeT m (ProxyFP a' a b' b) r.

Fixpoint runEffect (n : nat) `(dflt : r)
  `{m : A -> Type} {H : Monad (Container m)}
  `(x : Proxy False unit unit False m r) {struct n} : Container m r :=
  match n with
  | S n =>
      match x with
      | runFreeT v =>
          y <- v ;
          match y return Container m r with
          | Pure r => pure r
          | Free {| shape  := Request _
                  ; getter := f |} => runEffect n dflt (f tt)
          | Free {| shape  := Respond _
                  ; getter := f |} => runEffect n dflt (f tt)
          end
      end
  | Z => pure dflt
  end.

Program Definition respond `{m : A -> Type} `{Monad (Container m)}
  {x' x a' a} (z : a) : Proxy x' x a' a m a' :=
  runFreeT $ pure/Container m $
    Free {| shape  := Respond a
          ; getter := runFreeT ∘ pure ∘ Pure |}.

Definition Producer  b := Proxy False unit unit b.
Definition Producer' b m r := forall x' x, Proxy x' x unit b m r.
