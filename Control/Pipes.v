Require Import Hask.Prelude.
Require Import Hask.Control.Lens.
Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.Trans.Free.

(* Set Universe Polymorphism. *)

Generalizable All Variables.

Inductive Proxy (a' a b' b : Type) (m : Type -> Type) (r : Type) : Type :=
    | Request of a' & (a  -> Proxy a' a b' b m r)
    | Respond of b  & (b' -> Proxy a' a b' b m r)
    | M : forall x, (x -> Proxy a' a b' b m r) -> m x
                       -> Proxy a' a b' b m r
    | Pure    of r.

Arguments Request {a' a b' b m r} _ _.
Arguments Respond {a' a b' b m r} _ _.
Arguments M {a' a b' b m r x} _ _.
Arguments Pure {a' a b' b m r} _.

Definition Proxy_bind {a' a b' b c d} `{Monad m}
  (f : c -> Proxy a' a b' b m d) (p0 : Proxy a' a b' b m c) :
  Proxy a' a b' b m d :=
  let fix go p := match p with
    | Request a' fa  => Request a' (go \o fa)
    | Respond b  fb' => Respond b  (go \o fb')
    | M _     f  t   => M (go \o f) t
    | Pure    r      => f r
    end in
  go p0.

Instance Proxy_Functor {a' a b' b} `{Monad m} :
  Functor (Proxy a' a b' b m) := {
  fmap := fun _ _ f p0 => Proxy_bind (Pure \o f) p0
}.

Instance Proxy_Applicative {a' a b' b} `{Monad m} :
  Applicative (Proxy a' a b' b m) := {
  pure := fun _ => Pure;
  ap   := fun _ _ pf px => Proxy_bind (flip fmap px) pf
}.

Instance Proxy_Monad {a' a b' b} `{Monad m} :
  Monad (Proxy a' a b' b m) := {
  join := fun _ x => Proxy_bind id x
}.

Fixpoint runEffect `{Monad m} `(p : Proxy False unit unit False m r) : m r :=
  match p with
  | Request v f => False_rect _ v
  | Respond v f => False_rect _ v
  | M _     f t => t >>= (runEffect \o f)
  | Pure    r   => pure r
  end.

Definition respond {x' x a' a m} (z : a) : Proxy x' x a' a m a' :=
  Respond z Pure.

Definition Producer := Proxy False unit unit.
Definition Producer' b m r := forall x' x, Proxy x' x unit b m r.

Definition yieldxx {a m} (z : a) : Producer' a m unit :=
  fun _ _ => respond z.
Definition yield {a x' x m} (z : a) : Proxy x' x unit a m unit :=
  @yieldxx a m z x' x.

Definition forP `{Monad m} {x' x a' b' b c' c} (p0 : Proxy x' x b' b m a')
  (fb : b -> Proxy x' x c' c m b') : Proxy x' x c' c m a' :=
  let fix go p := match p with
    | Request x' fx  => Request x' (go \o fx)
    | Respond b  fb' => fb b >>= (go \o fb')
    | M _     f  t   => M (go \o f) t
    | Pure       a   => Pure a
    end in
  go p0.

Notation "x //> y" := (forP x y) (at level 60).

Notation "f />/ g" := (fun a => f a //> g) (at level 60).

Definition each `{Monad m} {a} : seq a -> Producer a m unit :=
  mapM_ yield.

Fixpoint toListM `{Monad m} `(p : Producer a m unit) : m (seq a) :=
  match p with
  | Request v _  => False_rect _ v
  | Respond x fu => cons x <$> toListM (fu tt)
  | M _     f t  => t >>= (toListM \o f)
  | Pure    _    => pure [::]
  end.

(* jww (2015-05-30): Make \o bind tighter than >>= *)

Module PipesLaws.

Include MonadLaws.

Require Import FunctionalExtensionality.

Tactic Notation "reduce_proxy" ident(IHu) tactic(T) :=
  elim=> [? ? IHu|? ? IHu|? ? IHu| ?]; T;
  try (try move => m0; f_equal; extensionality RP_A; exact: IHu).

Program Instance Proxy_FunctorLaws {a' a b' b} `{MonadLaws m} :
  FunctorLaws (Proxy a' a b' b m).
Obligation 1. by reduce_proxy IHx simpl. Qed.
Obligation 2. by reduce_proxy IHx simpl. Qed.

Program Instance Proxy_ApplicativeLaws {a' a b' b} `{MonadLaws m} :
  ApplicativeLaws (Proxy a' a b' b m).
Obligation 1. reduce_proxy IHx (rewrite /flip /=). Qed.
Obligation 2.
  rewrite /flip.
  move: u; reduce_proxy IHu simpl.
  move: v; reduce_proxy IHv simpl.
  by move: w; reduce_proxy IHw simpl.
Admitted.

Program Instance Proxy_MonadLaws {a' a b' b} `{MonadLaws m} :
  MonadLaws (Proxy a' a b' b m).
Obligation 1. by reduce_proxy IHx simpl. Qed.
Obligation 2. by reduce_proxy IHx simpl. Qed.
Obligation 4. by reduce_proxy IHx simpl. Qed.

Theorem respond_distrib `{MonadLaws m} :
  forall (x' x a' a b' b c' c r : Type)
         (f : a  -> Proxy x' x b' b m a')
         (g : a' -> Proxy x' x b' b m r)
         (h : b  -> Proxy x' x c' c m b'),
  (f >=> g) />/ h =1 (f />/ h) >=> (g />/ h).
Proof.
  move=> ? ? ? ? ? ? ? ? ? f ? ? x.
  rewrite /kleisli_compose.
  elim: (f x) => // [? ? IHx|? ? IHx|? ? IHx].
  - rewrite /bind /=.
    f_equal.
    extensionality a1.
    exact: IHx.
  - apply functional_extensionality in IHx.
    by rewrite /= /funcomp IHx /bind /funcomp
               -join_fmap_fmap_x fmap_comp_x
               -join_fmap_join_x fmap_comp_x.
  - move=> m0.
    rewrite /bind /=.
    f_equal.
    extensionality y.
    exact: IHx.
Qed.

Require Import Hask.Control.Category.

Program Instance Respond_Category {x' x a'} `{MonadLaws m} : Category := {
  ob     := Type;
  hom    := fun A B => A -> Proxy x' x a' B m a';
  c_id   := fun A => @respond x' x a' A m;
  c_comp := fun _ _ _ f g => g />/ f
}.
Obligation 1. (* Right identity *)
  extensionality z.
  exact: join_fmap_pure_x.
Qed.
Obligation 2. (* Left identity *)
  extensionality z.
  move: (f z).
  by reduce_proxy IHx (rewrite /= /bind /funcomp /=).
Qed.
Obligation 3. (* Associativity *)
  extensionality z.
  elim: (h z) => // [? ? IHx|? ? IHx|? ? IHx].
  - rewrite /=.
    f_equal.
    extensionality a1.
    exact: IHx.
  - apply functional_extensionality in IHx.
    by rewrite /= /funcomp -IHx respond_distrib.
  - move=> m0.
    rewrite /=.
    f_equal.
    rewrite /funcomp.
    extensionality y.
    exact: IHx.
Qed.

Section GeneralTheorems.

Theorem toListM_each_id : forall a, toListM \o each =1 pure (a:=seq a).
Proof.
  move=> a xs.
  elim: xs => //= [x xs IHxs].
  by rewrite IHxs.
Qed.

End GeneralTheorems.

End PipesLaws.