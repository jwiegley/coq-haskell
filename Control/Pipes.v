Require Import Hask.Prelude.
Require Import Hask.Control.Lens.
Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.Trans.Free.
Require Import Hask.Data.Functor.Identity.

(* Set Universe Polymorphism. *)

Generalizable All Variables.

Inductive ProxyF a' a b' b r :=
  | Request of a' & (a  -> r)
  | Respond of b  & (b' -> r).
Arguments Request {a' a b' b r} _ _.
Arguments Respond {a' a b' b r} _ _.

Program Instance ProxyF_Functor : Functor (ProxyF a' a b' b) := {
  fmap := fun _ _ f x => match x with
    | Request a' fa => Request a' (f \o fa)
    | Respond b  fb => Respond b  (f \o fb)
    end
}.

Definition Proxy a' a b' b m r := FreeT (ProxyF a' a b' b) m r.

Definition runEffect `{Monad m} `(p : Proxy False unit unit False m r) : m r :=
  p _ pure $ fun _ k x => match x with
    | Request _ f => k (f tt)
    | Respond _ f => k (f tt)
    end.

Definition respond `{Monad m} `(z : a) {x' x a'} : Proxy x' x a' a m a' :=
  fun _ k g => g _ id $ Respond z k.

Definition Producer  b m r := Proxy False unit unit b m r.
Definition Producer' b m r := forall x' x, Proxy x' x unit b m r.

Definition yieldxx `{Monad m} {a} (z : a) : Producer' a m unit :=
  fun _ _ => respond z.
Definition yield `{Monad m} {a x' x} (z : a) : Proxy x' x unit a m unit :=
  @yieldxx m _ a z x' x.

Definition forP `{Monad m} `(p0 : Proxy x' x b' b m a')
  `(fb : b -> Proxy x' x c' c m b') : Proxy x' x c' c m a' :=
  fun _ k g => p0 _ k $ fun _ h x => match x with
    | Request x' fx  => g _ h $ Request x' fx
    | Respond b  fb' => fb b _ (h \o fb') g
    end.

Notation "x //> y" := (forP x y) (at level 60).

Definition each `{Monad m} {a} : seq a -> Producer a m unit :=
  mapM_ yield.
  (* @mapM_ (FreeT (ProxyF False unit unit a) m) *)
  (*        (@FreeT_Monad (ProxyF False unit unit a) m) _ _ yield. *)

Definition toListM `{Monad m} `(p : Producer a m unit) : m (seq a) :=
  p _ (fun _ => pure [::]) $ fun X h p => match p with
    | Request v f  => h (f tt)
    | Respond x f => @fmap m _ _ _ (cons x) (h (f tt))
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
Abort.

(* main :: IO () *)
(* main = do *)
(*     runEffect $ for (each [1..4 :: Int]) (lift . print) *)
(*     runEffect $ for stdinLn (lift . putStrLn) *)

End Examples.

End PipesLaws.