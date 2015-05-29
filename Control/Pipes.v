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

Definition runEffect `{Applicative m}
  `(p : Proxy False unit unit False m r) : m r :=
  p _ pure $ fun _ k x => match x with
    | Request _ f => k (f tt)
    | Respond _ f => k (f tt)
    end.

Definition respond `(z : a) {x' x a' m} : Proxy x' x a' a m a' :=
  fun _ k g => g _ id $ Respond z k.

Definition Producer  b m r := Proxy False unit unit b m r.
Definition Producer' b m r := forall x' x, Proxy x' x unit b m r.

Definition yieldxx {a m} (z : a) : Producer' a m unit :=
  fun _ _ => respond z.
Definition yield {a x' x m} (z : a) : Proxy x' x unit a m unit :=
  @yieldxx a m z x' x.

Definition forP `(p0 : Proxy x' x b' b m a')
  `(fb : b -> Proxy x' x c' c m b') : Proxy x' x c' c m a' :=
  fun _ k g => p0 _ k $ fun _ h x => match x with
    | Request x' fx  => g _ h $ Request x' fx
    | Respond b  fb' => fb b _ (h \o fb') g
    end.

Notation "x //> y" := (forP x y) (at level 60).

Definition each {a m} : seq a -> Producer a m unit :=
  mapM_ yield.

Definition toListM `{Applicative m} `(p : Producer a m unit) : m (seq a) :=
  p _ (fun _ => pure [::]) $ fun X h p => match p with
    | Request v f  => h (f tt)
    | Respond x f => @fmap m _ _ _ (cons x) (h (f tt))
    end.

Module PipesLaws.

Include MonadLaws.

Section Examples.

Example toListM_ex1 : @toListM id _ _ (yield 1) = [:: 1].
Proof. reflexivity. Qed.

Example toListM_ex2 : @toListM id _ _ (yield 1 ;; yield 2) = [:: 1; 2].
Proof. reflexivity. Qed.

Example toListM_ex3 : @toListM id _ _ (mapM_ yield [:: 1; 2]) = [:: 1; 2].
Proof. reflexivity. Qed.

Example toListM_ex4 : @toListM id _ _ (each [:: 1; 2]) = [:: 1; 2].
Proof. reflexivity. Qed.

Axiom FreeT_fmap :
  forall `{Monad m} a r (g : r -> r) f (l : FreeT f m a) k h,
  @fmap m _ _ _ g (l r k h) = l r k (fun n s => @fmap m _ _ _ g \o h n s).

Variable f : Type -> Type.
Context `{Functor f}.
Context `{FunctorLaws f}.

Variable m : Type -> Type.
Context `{HM : Monad m}.
Context `{MonadLaws m}.

Theorem toListM_each : forall a (xs : seq a), toListM (each xs) = pure xs.
Proof.
  move=> a xs.
  elim: xs => //= [x xs IHxs].
  rewrite -ap_homo -IHxs ap_fmap_ext.
  rewrite FreeT_fmap /funcomp /=.
  rewrite /each /mapM_ /= -/mapM.
  rewrite /toListM.
  (* set k := (X in mapM_ yield xs _ _ X). *)
  set g := (X in _ _ X = _).
  (* set l := mapM_ yield xs. *)
  set r := seq a.
  (* rewrite fmap_pure_x. *)
Abort.

End Examples.

End PipesLaws.