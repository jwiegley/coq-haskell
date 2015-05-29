Require Import Hask.Prelude.
Require Import Hask.Control.Lens.
Require Import Hask.Control.Monad.
Require Import Hask.Data.Functor.Container.

Generalizable All Variables.

Definition Mu (f : Type -> Type) := forall r, (f r -> r) -> r.

Inductive ProxyF (a' a b' b : Type) (m : Type -> Type) (r k : Type) :=
  | Request of a' & (a  -> k)
  | Respond of b  & (b' -> k)
  | M of m k
  | Pure of r.

Arguments Request {a' a b' b m r k} _ _.
Arguments Respond {a' a b' b m r k} _ _.
Arguments M {a' a b' b m r k} _.
Arguments Pure {a' a b' b m r k} _.

Program Instance ProxyF_Functor {a' a b' b m} `{Monad m} :
  Functor (fun r => ProxyF a' a b' b m r k) := {
  fmap := fun _ _ f x => match x with
    | Request a' fa  => Request a' fa
    | Respond b  fb' => Respond b  fb'
    | M          m   => M m
    | Pure    r      => Pure (f r)
    end
}.

Definition Proxy a' a b' b `(m : Type -> Type) (r : Type) :=
  Mu (ProxyF a' a b' b m r).

Program Instance Proxy_Functor {a' a b' b m} `{Monad m} :
  Functor (Proxy a' a b' b m) := {
  fmap := fun _ _ f p => fun s k => p s $ fun x => k $ fmap f x
}.

Program Instance Proxy_Applicative {a' a b' b m} `{Monad m} :
  Applicative (Proxy a' a b' b m) := {
  pure := fun _ x => fun _ k => k $ Pure x;
  ap   := fun _ _ pf px =>
    fun s k => pf _ $ fun f => k $ match f with
    | Request a' fa  => Request a' fa
    | Respond b  fb' => Respond b  fb'
    | M          m   => M m
    | Pure    f      => undefined
    end
}.

Program Instance Proxy_Monad {a' a b' b m} `{Monad m} :
  Monad (Proxy a' a b' b m) := {
  join := fun _ x => undefined
}.

(* The final encoding form of Mu is directly related to the catamorphism. *)
Definition cata `{Functor f} `(k : f a -> a) (x : Mu f) : a := x _ k.

Definition runEffect `{Monad m} `(p : Proxy False unit unit False m r) : m r :=
  p (m r) $ fun x => match x with
    | Request _ f => f tt
    | Respond _ f => f tt
    | M m         => join m
    | Pure r      => pure r
    end.

Definition respond `{Monad m} `(z : a) {x' x a'} : Proxy x' x a' a m a' :=
  fun _ k => k $ Respond z (k \o Pure).

Definition Producer  b m r := Proxy False unit unit b m r.
Definition Producer' b m r := forall x' x, Proxy x' x unit b m r.

Definition yieldxx `{Monad m} {a} (z : a) : Producer' a m unit :=
  fun _ _ => respond z.
Definition yield `{Monad m} {a x' x} (z : a) : Proxy x' x unit a m unit :=
  @yieldxx m _ a z x' x.

Definition forP `{Monad m} `(p0 : Proxy x' x b' b m a')
  `(fb : b -> Proxy x' x c' c m b') : Proxy x' x c' c m a' :=
  fun _ k => p0 _ $ fun x => match x with
    | Request x' fx  => k $ Request x' fx
(*
p0 : Proxy x' x b' b m a'
c' : Type
c : Type
fb : b -> Proxy x' x c' c m b'
s : Type
k : ProxyF x' x c' c m a' s -> s
x0 : ProxyF x' x b' b m a' s
b0 : b
fb' : b' -> s
*)
    | Respond b  fb' => fb b _ (k \o fb')
    | M       x      => k $ M x
    | Pure    a      => k $ Pure a
    end.

Notation "x //> y" := (forP x y) (at level 60).

Definition each `{Monad m} {a} : seq a -> Producer a m unit :=
  mapM_ yield.
  (* @mapM_ (FreeT (ProxyF False unit unit a) m) *)
  (*        (@FreeT_Monad (ProxyF False unit unit a) m) _ _ yield. *)

Definition toListM `{Monad m} `(p : Producer a m unit) : m (seq a) :=
  p (m (seq a)) $ fun x => match x return m (seq a) with
    | Request v f => f tt
    | Respond x f => fmap (cons x) (f tt)
    | M m         => join m
    | Pure a      => pure [::]
    end.

Module PipesLaws.

Include MonadLaws.

Section Examples.

Variable f : Type -> Type.
Context `{HF : Functor f}.

Variable m : Type -> Type.
Context `{H : Monad m}.
Context `{HL : MonadLaws m}.

(* Lemma FreeT_fmap : forall (a b d : Type) *)
(*   (n : a -> m b) (c : forall x, (x -> m b) -> f x -> m b) *)
(*   (l : FreeT f m a) (g : b -> d), *)
(*   @fmap m _ b d g (l b n c) *)
(*     = l d (@fmap m _ b d g \o n) (fun s k h => c s (k \o g) h). *)
(* Proof. by []. Qed. *)

Example toListM_each : forall a (xs : seq a), toListM (each xs) = pure xs.
Proof.
  move=> a xs.
  elim: xs => //= [x xs IHxs].
  rewrite -ap_homo -IHxs ap_fmap_ext.
  rewrite /each /mapM_ /= -/mapM_.
  rewrite /toListM.
Abort.

(* main :: IO () *)
(* main = do *)
(*     runEffect $ for (each [1..4 :: Int]) (lift . print) *)
(*     runEffect $ for stdinLn (lift . putStrLn) *)

End Examples.

End PipesLaws