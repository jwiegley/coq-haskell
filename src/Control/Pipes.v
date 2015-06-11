Require Import Hask.Prelude.
Require Import Hask.Control.Lens.
Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.Trans.Free.

Generalizable All Variables.

(****************************************************************************
 *
 * Proxy
 *)

Inductive Proxy (a' a b' b : Type) (m : Type -> Type) (r : Type) : Type :=
  | Request of a' & (a  -> Proxy a' a b' b m r)
  | Respond of b  & (b' -> Proxy a' a b' b m r)
  | M : forall x, (x -> Proxy a' a b' b m r) -> m x -> Proxy a' a b' b m r
  | Pure of r.

Arguments Request {a' a b' b m r} _ _.
Arguments Respond {a' a b' b m r} _ _.
Arguments M {a' a b' b m r x} _ _.
Arguments Pure {a' a b' b m r} _.

(****************************************************************************
 *
 * Fundamental code to operate with Proxy's
 *)

Definition foldProxy `{Monad m}
  `(ka : a' -> (a  -> s) -> s)
  `(kb : b  -> (b' -> s) -> s)
  `(km : forall x, (x -> s) -> m x -> s)
  `(kp : r -> s)
  (p : Proxy a' a b' b m r) : s :=
  let fix go p := match p with
    | Request a' fa  => ka a' (go \o fa)
    | Respond b  fb' => kb b  (go \o fb')
    | M _     g  h   => km _  (go \o g) h
    | Pure    r      => kp r
    end in
  go p.

(* This is equivalent to [foldProxy Request Respond (fun _ => M)], but using
   that definition makes some proofs harder. *)
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

Instance Proxy_Functor `{Monad m} {a' a b' b} :
  Functor (Proxy a' a b' b m) := {
  fmap := fun _ _ f => Proxy_bind (Pure \o f)
}.

Instance Proxy_Applicative `{Monad m} {a' a b' b} :
  Applicative (Proxy a' a b' b m) := {
  pure := fun _ => Pure;
  ap   := fun _ _ pf px => Proxy_bind (fmap ^~ px) pf
}.

Instance Proxy_Monad `{Monad m} {a' a b' b} :
  Monad (Proxy a' a b' b m) := {
  join := fun _ => Proxy_bind id
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

Definition request {x' x a' a m} (z : x') : Proxy x' x a' a m x :=
  Request z Pure.

Definition Producer := Proxy False unit unit.
Definition Producer' b m r := forall x' x, Proxy x' x unit b m r.

Definition yield {a x' x m} (z : a) : Proxy x' x unit a m unit :=
  let go : Producer' a m unit := fun _ _ => respond z in @go x' x.

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

Definition rofP `{Monad m} {y' y a' a b' b c} (fb' : b' -> Proxy a' a y' y m b)
  (p0 : Proxy b' b y' y m c) : Proxy a' a y' y m c :=
  let fix go p := match p with
    | Request b' fb  => fb' b' >>= (go \o fb)
    | Respond x  fx' => Respond x (go \o fx')
    | M _     f  t   => M (go \o f) t
    | Pure       a   => Pure a
    end in
  go p0.

Notation "x >\\ y" := (rofP x y) (at level 60).

Notation "f \>\ g" := (fun a => f >\\ g a) (at level 60).

Fixpoint pushR `{Monad m} {a' a b' b c' c r} (p0 : Proxy a' a b' b m r)
  (fb : b -> Proxy b' b c' c m r) {struct p0} : Proxy a' a c' c m r :=
  match p0 with
  | Request a' fa  => Request a' (flip pushR fb \o fa)
  | Respond b  fb' =>
      let fix go' p := match p with
        | Request b' fb  => pushR (fb' b') fb
        | Respond c  fc' => Respond c (go' \o fc')
        | M _     f  t   => M (go' \o f) t
        | Pure       a   => Pure a
        end in
      go' (fb b)
  | M _     f  t   => M (flip pushR fb \o f) t
  | Pure       a   => Pure a
  end.

Notation "x >>~ y" := (pushR x y) (at level 60).

Notation "f >~> g" := (fun a => f a >>~ g) (at level 60).

Fixpoint pullR `{Monad m} {a' a b' b c' c r} (fb' : b' -> Proxy a' a b' b m r)
  (p0 : Proxy b' b c' c m r) {struct p0} : Proxy a' a c' c m r :=
  match p0 with
  | Request b' fb  =>
      let fix go' p := match p with
        | Request a' fa  => Request a' (go' \o fa)
        | Respond b  fb' => pullR fb' (fb b)
        | M _     f  t   => M (go' \o f) t
        | Pure       a   => Pure a
        end in
      go' (fb' b')
  | Respond c  fc' => Respond c (pullR fb' \o fc')
  | M _     f  t   => M (pullR fb' \o f) t
  | Pure       a   => Pure a
  end.

Notation "x +>> y" := (pullR x y) (at level 60).

Notation "f >+> g" := (fun a => f +>> g a) (at level 60).

Definition reflect `{Monad m} `(p : Proxy a' a b' b m r) :
  Proxy b b' a a' m r :=
  let fix go p := match p with
    | Request a' fa  => Respond a' (go \o fa)
    | Respond b  fb' => Request b  (go \o fb')
    | M _     g  h   => M (go \o g) h
    | Pure    r      => Pure r
    end in
  go p.

(****************************************************************************
 *
 * General routines
 *)

Definition each `{Monad m} {a} : seq a -> Producer a m unit := mapM_ yield.

Fixpoint toListM `{Monad m} `(p : Producer a m unit) : m (seq a) :=
  match p with
  | Request v _  => False_rect _ v
  | Respond x fu => cons x <$> toListM (fu tt)
  | M _     f t  => t >>= (toListM \o f)
  | Pure    _    => pure [::]
  end.

(****************************************************************************
 ****************************************************************************
 **                                                                        **
 ** Proofs of the pipes categories and laws                                **
 **                                                                        **
 ****************************************************************************
 ****************************************************************************)

Module PipesLaws.

Include MonadLaws.

Require Import Hask.Control.Category.
Require Import FunctionalExtensionality.

Tactic Notation "reduce_proxy" ident(IHu) tactic(T) :=
  elim=> [? ? IHu|? ? IHu|? ? IHu| ?]; T;
  try (try move => m0; f_equal; extensionality RP_A; exact: IHu).

(****************************************************************************
 *
 * Kleisli Category for Proxy a' a b' b m
 *)

Section Kleisli.

Global Program Instance Proxy_FunctorLaws `{MonadLaws m} {a' a b' b} :
  FunctorLaws (Proxy a' a b' b m).
Obligation 1. by reduce_proxy IHx simpl. Qed.
Obligation 2. by reduce_proxy IHx simpl. Qed.

Global Program Instance Proxy_ApplicativeLaws `{MonadLaws m} {a' a b' b} :
  ApplicativeLaws (Proxy a' a b' b m).
Obligation 1. by reduce_proxy IHx simpl. Qed.
Obligation 2.
  move: u; reduce_proxy IHu (rewrite /funcomp /= /funcomp).
  move: v; reduce_proxy IHv (rewrite /funcomp /= /funcomp).
  by move: w; reduce_proxy IHw simpl.
Qed.

Global Program Instance Proxy_MonadLaws `{MonadLaws m} {a' a b' b} :
  MonadLaws (Proxy a' a b' b m).
Obligation 1. by reduce_proxy IHx simpl. Qed.
Obligation 2. by reduce_proxy IHx simpl. Qed.
Obligation 4. by reduce_proxy IHx simpl. Qed.

End Kleisli.

(****************************************************************************
 *
 * Respond Category
 *)

Section Respond.

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

Corollary respond_zero `{MonadLaws m} : forall `(f : c -> Proxy a' a b' b m r),
  pure />/ f =1 @pure _ Proxy_Applicative r.
Proof. by []. Qed.

End Respond.

(****************************************************************************
 *
 * Request Category
 *)

Section Request.

Theorem request_distrib `{MonadLaws m} :
  forall (y' y a' a b' b c' c r : Type)
         (f : c -> Proxy b' b y' y m c')
         (g : c'  -> Proxy b' b y' y m r)
         (h : b' -> Proxy a' a y' y m b),
  h \>\ (f >=> g) =1 (h \>\ f) >=> (h \>\ g).
Proof.
  move=> ? ? ? ? ? ? ? ? ? f ? ? x.
  rewrite /kleisli_compose.
  elim: (f x) => // [? ? IHx|? ? IHx|? ? IHx].
  - apply functional_extensionality in IHx.
    by rewrite /= /funcomp IHx /bind /funcomp
               -join_fmap_fmap_x fmap_comp_x
               -join_fmap_join_x fmap_comp_x.
  - rewrite /bind /=.
    f_equal.
    extensionality a1.
    exact: IHx.
  - move=> m0.
    rewrite /bind /=.
    f_equal.
    extensionality y.
    exact: IHx.
Qed.

Program Instance Request_Category {x a' a} `{MonadLaws m} : Category := {
  ob     := Type;
  hom    := fun A B => B -> Proxy A x a' a m x;
  c_id   := fun A => @request A x a' a m;
  c_comp := fun _ _ _ f g => g \>\ f
}.
Obligation 1. (* Right identity *)
  extensionality z.
  move: (f z).
  by reduce_proxy IHx (rewrite /= /bind /funcomp /=).
Qed.
Obligation 2. (* Left identity *)
  extensionality z.
  exact: join_fmap_pure_x.
Qed.
Obligation 3. (* Associativity *)
  extensionality z.
  elim: (f z) => // [y p IHx|? ? IHx|? ? IHx].
  - apply functional_extensionality in IHx.
    by rewrite /= /funcomp IHx request_distrib.
  - rewrite /=.
    f_equal.
    extensionality a1.
    exact: IHx.
  - move=> m0.
    rewrite /=.
    f_equal.
    rewrite /funcomp.
    extensionality y.
    exact: IHx.
Qed.

Corollary request_zero `{MonadLaws m} : forall `(f : c -> Proxy a' a b' b m r),
  f \>\ pure =1 @pure _ Proxy_Applicative r.
Proof. by []. Qed.

End Request.

(****************************************************************************
 *
 * Push Category
 *)

Tactic Notation "reduce_over" constr(f) ident(g) ident(y) ident(IHx) :=
  move=> ? ? ? ? ? ? ? ? g ?;
  rewrite /= /funcomp;
  congr (f _ _);
  extensionality y;
  move: (g y);
  by reduce_proxy IHx simpl.

Section Push.

(*
Inductive push_eventually {m r} :
  forall a' a b' b, Proxy a' a b' b m r -> Prop :=
  | ev_pushR_req  : forall a' a b' b (aa' : a') (fa : a -> Proxy a' a b' b m r),
                      push_eventually a' a b' b (Request aa' fa)
  (* | ev_pushR_res  : forall a' a b' b c' c (bb : b) *)
  (*                     (fb' : b' -> Proxy a' a b' b m r) *)
  (*                     (fb : b -> Proxy b' b c' c m r), *)
  (*                     pull_eventually b' b c' c (fb bb) -> *)
  (*                     push_eventually a' a b' b (Respond bb fb') *)
  | ev_pushR_mon  : forall a' a b' b x (g : x -> Proxy a' a b' b m r) (h : m x),
                      push_eventually a' a b' b (M g h)
  | ev_pushR_pure : forall a' a b' b (x : r), push_eventually a' a b' b (Pure x)

with pull_eventually {m r} : forall a' a b' b, Proxy a' a b' b m r -> Prop :=
  (* | ev_pullR_req  : forall a' a b' b c' c (aa' : a') *)
  (*                     (fa : a -> Proxy a' a b' b m r) *)
  (*                     (fa' : a' -> Proxy c' c a' a m r), *)
  (*                     push_eventually c' c a' a (fa' aa') -> *)
  (*                     pull_eventually a' a b' b (Request aa' fa) *)
  | ev_pullR_res  : forall a' a b' b (bb : b) (fb' : b' -> Proxy a' a b' b m r),
                      pull_eventually a' a b' b (Respond bb fb')
  | ev_pullR_mon  : forall a' a b' b x (g : x -> Proxy a' a b' b m r) (h : m x),
                      pull_eventually a' a b' b (M g h)
  | ev_pullR_pure : forall a' a b' b (x : r),
                      pull_eventually a' a b' b (Pure x).

Arguments ev_pushR_req {m r a' a b' b} aa' fa.
(* Arguments ev_pushR_res {m r a' a b' b c' c} bb fb' fb _. *)
Arguments ev_pushR_mon {m r a' a b' b} x g h.
Arguments ev_pushR_pure {m r a' a b' b} x.

(* Arguments ev_pullR_req {m r a' a b' b c' c} aa' fa fa' _. *)
Arguments ev_pullR_res {m r a' a b' b} bb fb'.
Arguments ev_pullR_mon {m r a' a b' b} x g h.
Arguments ev_pullR_pure {m r a' a b' b} x.

Definition push_render `{Monad m}
  `(p : Proxy a' a b' b m r)
  `(fb : b -> Proxy b' b c' c m r) : push_eventually a' a b' b p :=
  let fix go p := match p with
    | Request aa' fa  => ev_pushR_req aa' fa
    | Respond bb  fb' =>
        match fb bb with
        | Request bb' fb  => go (fb' bb')
        | Respond cc  fc' => ev_pullR_res cc fc'
        | M x     g   h   => ev_pullR_mon x g h
        | Pure    r       => ev_pullR_pure r
        end
    | M x     g   h   => ev_pushR_mon x g h
    | Pure    r       => ev_pushR_pure r
    end in
  go p.

with pull_render  {a' a b' b c' c r} `{Monad m}
  (fb' : b' -> Proxy a' a b' b m r)
  (p : Proxy b' b c' c m r) {struct p} : pull_eventually b' b c' c p :=

Compute @push_eventually unit unit unit unit id unit
  (Respond tt (fun _ : unit => Respond tt (fun _ : unit => Pure tt))).
*)

Lemma push_request `{Monad m} :
  forall `(f : b -> Proxy b' b c' c m r)
         `(g : a -> Proxy a' a b' b m r) x,
  Request x g >>~ f = Request x (g >~> f).
Proof. reduce_over @Request g y IHx. Qed.

Lemma push_m `{Monad m} :
  forall `(f : b -> Proxy b' b c' c m r)
         `(g : x -> Proxy a' a b' b m r) (h : m x),
  M g h >>~ f = M (g >~> f) h.
Proof. move=> x; reduce_over @M g y IHx. Qed.

Program Instance Push_Category `{MonadLaws m} {r : Type} :
  Category := {
  ob     := Type * Type;
  hom    := fun A B => snd A -> Proxy (fst A) (snd A) (fst B) (snd B) m r;
  c_id   := fun A => undefined;
  c_comp := fun _ _ _ f g => g >~> f
}.
Obligation 1. (* Right identity *)
Admitted.
Obligation 2. (* Left identity *)
Admitted.
Obligation 3. (* Associativity *)
  simpl in *.
  extensionality z.
  move: f g.
  elim: (h z) => // [? ? IHx|b fb' IHx|? ? IHx] f g.
  - rewrite 3!push_request.
    congr (Request _ _).
    extensionality w.
    exact: IHx.
  - rewrite /=.
    move: f.
    move: (g b).
    reduce_proxy IHy (rewrite /= /flip /funcomp /=) => f.
    + exact: IHx.
    + move: (f _).
      reduce_proxy IHz (rewrite /= /flip /funcomp /=).
      exact: IHy.
  - move=> m0.
    rewrite 3!push_m.
    congr (M _ _).
    extensionality w.
    exact: IHx.
Qed.

End Push.

(****************************************************************************
 *
 * Pull Category
 *)

Section Pull.

Lemma pull_respond `{Monad m} :
  forall `(f : b' -> Proxy a' a b' b m r)
         `(g : c' -> Proxy b' b c' c m r) x,
  f +>> Respond x g = Respond x (f >+> g).
Proof. reduce_over @Respond g y IHx. Qed.

Lemma pull_m `{Monad m} :
  forall x `(f : b' -> Proxy a' a b' b m r)
         `(g : x -> Proxy b' b c' c m r) (h : m x),
  f +>> M g h = M (f >+> g) h.
Proof. move=> x; reduce_over @M g y IHx. Qed.

Program Instance Pull_Category `{MonadLaws m} {r : Type} : Category := {
  ob     := Type * Type;
  hom    := fun A B => fst A -> Proxy (fst B) (snd B) (fst A) (snd A) m r;
  c_id   := fun A => undefined;
  c_comp := fun _ _ _ f g => f >+> g
}.
Obligation 1. (* Right identity *)
Admitted.
Obligation 2. (* Left identity *)
Admitted.
Obligation 3. (* Associativity *)
  simpl in *.
  extensionality z.
  move: f g.
  elim: (h z) => // [a' fa IHx|? ? IHx|? ? IHx] f g.
  - rewrite /=.
    move: f.
    move: (g a').
    reduce_proxy IHy (rewrite /= /flip /funcomp /=) => f.
    + move: (f _).
      reduce_proxy IHz (rewrite /= /flip /funcomp /=).
      exact: IHy.
    + exact: IHx.
  - rewrite 3!pull_respond.
    congr (Respond _ _).
    extensionality w.
    exact: IHx.
  - move=> m0.
    rewrite 3!pull_m.
    congr (M _ _).
    extensionality w.
    exact: IHx.
Qed.

Theorem push_pull_assoc `{MonadLaws m} :
  forall `(f : b' -> Proxy a' a b' b m r)
         `(g : a  -> Proxy b' b c' c m r)
          (h : c  -> Proxy c' c b' b m r),
  (f >+> g) >~> h =1 f >+> (g >~> h).
Proof.
  move=> ? ? ? ? ? f ? ? g h a.
  move: f h.
  elim: (g a) => // [a' fa IHx|b fb' IHx|? ? IHx] => f h.
  - rewrite push_request.
    rewrite /=.
    move: h.
    move: (f a').
    reduce_proxy IHy (rewrite /= /flip /funcomp /=) => h.
    exact: IHx.
  - rewrite pull_respond.
    rewrite /=.
    move: f.
    move: (h b).
    reduce_proxy IHy (rewrite /= /flip /funcomp /=) => f.
    exact: IHx.
  - move=> m0.
    rewrite pull_m push_m push_m pull_m.
    congr (M _ f).
    extensionality w.
    exact: IHx.
Qed.

End Pull.

(****************************************************************************
 *
 * Reflection (Duals)
 *)

Section Duals.

Variables a' a b' b r : Type.
Variables m : Type -> Type.
Context `{MonadLaws m}.

Theorem request_id : reflect \o request =1 @respond a' a b' b m.
Proof. move=> x; by congr (Respond _ _). Qed.

Theorem reflect_distrib :
  forall (f : a -> Proxy a' a b' b m r)
         (g : r -> Proxy a' a b' b m r) (x : a),
    reflect (f x >>= g) = reflect (f x) >>= (reflect \o g).
Proof.
  move=> f g x.
  move: (f x).
  by reduce_proxy IHx (rewrite /bind /=).
Qed.

Theorem request_comp :
  forall (f : a -> Proxy a' a b' b m r)
         (g : a -> Proxy a  r b' b m r),
    reflect \o (f \>\ g) =1 (reflect \o g) />/ (reflect \o f).
Proof.
  move=> f g x.
  rewrite /=.
  move: (g x).
  reduce_proxy IHx simpl.
  move/functional_extensionality in IHx.
  by rewrite /funcomp -IHx reflect_distrib.
Qed.

Theorem respond_id : reflect \o respond =1 @request a' a b' b m.
Proof. move=> x; by congr (Request _ _). Qed.

Theorem respond_comp :
  forall (f : a -> Proxy a' a b' b m r)
         (g : b -> Proxy a' a b' b m b'),
    reflect \o (f />/ g) =1 (reflect \o g) \>\ (reflect \o f).
Proof.
  move=> f g x.
  rewrite /=.
  move: (f x).
  reduce_proxy IHx simpl.
  move/functional_extensionality in IHx.
  (* jww (2015-06-09): We should be able to use [reflect_distrib] here, but
     the types are not general enough, which means that the types of some of
     these theorems are probably incorrect. *)
  rewrite /funcomp -IHx.
  move: (g _).
  by reduce_proxy IHy (rewrite /bind /=).
Qed.

Corollary distributivity :
  forall (f : a -> Proxy a' a b' b m r)
         (g : r -> Proxy a' a b' b m r),
    reflect \o (f >=[Proxy_Monad]=> g) =1 (reflect \o f) >=> (reflect \o g).
Proof. exact: reflect_distrib. Qed.

Theorem zero_law : @reflect m _ a' a b' b r \o pure =1 pure.
Proof. by []. Qed.

Theorem involution : @reflect m _ a' a b' b r \o reflect =1 id.
Proof. by reduce_proxy IHx simpl. Qed.

End Duals.

(****************************************************************************
 *
 * General theorems about functions in the pipes library.
 *)

Section GeneralTheorems.

Theorem toListM_each_id : forall a, toListM \o each =1 pure (a:=seq a).
Proof.
  move=> a xs.
  elim: xs => //= [x xs IHxs].
  by rewrite IHxs.
Qed.

End GeneralTheorems.

(****************************************************************************
 *
 * Alternate presentation of Proxy, using a Boehm-Berarducci encoding
 *
 * In this form, we see that proxies are a kind of relation between three
 * natural transformations of hom-functors.
 *)

Section SProxy.

Definition SProxy (a' a b' b : Type) (m : Type -> Type) (r : Type) : Type :=
  forall s : Type,
       (a' -> (a  -> s) -> s)           (* SRequest *)
    -> (b  -> (b' -> s) -> s)           (* SRespond *)
    -> (forall x, (x -> s) -> m x -> s) (* SM *)
    -> (r -> s)                         (* SPure *)
    -> s.

Definition ftrans (a b x : Type) := a -> (b -> x) -> x.
Notation "a -[ s ]-> b" := (ftrans a b s) (at level 50).

Definition fnat (f g : Type -> Type) (s : Type) := forall x, (f x) -[s]-> (g x).
Notation "f -[[ s ]]-> g" := (fnat f g s) (at level 50).

Definition Proxy_ (a' a b' b : Type) (m : Type -> Type) (r : Type) : Type :=
  forall s : Type,
      a' -[s]->  a  ->
      b  -[s]->  b' ->
      m -[[s]]-> id ->
   unit  -[s]->  r.

Definition toProxy `(s : SProxy a' a b' b m r) : Proxy a' a b' b m r :=
  s _ Request Respond (fun _ => M) Pure.

Definition fromProxy `(p : Proxy a' a b' b m r) : SProxy a' a b' b m r :=
  fun _ req res mon k =>
    let fix go p := match p with
    | Request a' fa  => req a' (go \o fa)
    | Respond b  fb' => res b  (go \o fb')
    | M _     g  h   => mon _  (go \o g) h
    | Pure    x      => k x
    end in
    go p.

Lemma SProxy_to_from : forall `(x : Proxy a' a b' b m r),
  toProxy (fromProxy x) = x.
Proof.
  move=> a' a b' b m r.
  reduce_proxy IHx
    (rewrite /toProxy;
     first [ congr (Request _)
           | congr (Respond _)
           | move=> m0; congr (M _)
           | congr (Pure _) ]).
Qed.

Axiom f_const : forall `(f : a -> (b -> s) -> s) (x : a) (y : s),
  f x (const y) = y.

Definition const_f `(f : (b -> s) -> a -> s) (x : a) (y : s) :
  f (const y) x = y := f_const (flip f) x y.

(* As 'k' is the only function that can produce an 's', it must be equal to
   reducing the SProxy. *)
Axiom SProxy_parametricity : forall `(sp : SProxy a' a b' b m r) (s : Type)
  (req : a' -> (a  -> s) -> s)
  (res : b  -> (b' -> s) -> s)
  (mon : forall x, (x -> s) -> m x -> s)
  (k : r -> s) (z : r),
  k z = sp s req res mon k.

Lemma SProxy_from_to : forall `(x : SProxy a' a b' b m r),
  fromProxy (toProxy x) = x.
Proof.
  move=> ? ? ? ? ? ? x.
  extensionality s.
  extensionality req.
  extensionality res.
  extensionality mon.
  extensionality k.
  move: (toProxy x).
  reduce_proxy IHx
    (rewrite /fromProxy /funcomp /=;
     try (move/functional_extensionality in IHx;
          try move=> m0;
          rewrite IHx ?f_const ?const_f)).
  exact: SProxy_parametricity.
Qed.

Theorem sproxy_ind :
  forall (a' a b' b : Type) (m : Type -> Type) (r : Type)
         (P : SProxy a' a b' b m r -> Prop),
   (forall (x : a') (f : a -> SProxy a' a b' b m r),
      P (fun s req res mon k => req x (fun a => f a s req res mon k))) ->
   (forall (x : b) (f : b' -> SProxy a' a b' b m r),
      P (fun s req res mon k => res x (fun b' => f b' s req res mon k))) ->
   (forall t (f : t -> SProxy a' a b' b m r) (x : m t),
      P (fun s req res mon k => mon _ (fun x => f x s req res mon k) x)) ->
   (forall (x : r), P (fun s _ _ _ k => k x)) ->
   forall p : SProxy a' a b' b m r, P p.
Proof.
  move=> ? ? ? ? ? ? ? Hreq Hres Hmon Hpure p.
  rewrite -(SProxy_from_to p).
  elim: (toProxy p) => [*|*|*|*].
  - exact: Hreq.
  - exact: Hres.
  - exact: Hmon.
  - exact: Hpure.
Qed.

(* Juggling the arguments *)

Definition SProxy2 (a' a b' b : Type) (m : Type -> Type) (r : Type) : Type :=
  forall s : Type,
       ((a  -> s) -> (a' -> s))           (* SRequest *)
    -> ((b' -> s) -> (b  -> s))           (* SRespond *)
    -> (forall x, (x -> s) -> (m x -> s)) (* SM *)
    -> ((r -> s) -> (unit -> s)).         (* SPure *)

(* Applying a special case of the Yoneda lemma, which says:

    Nat(h^a, h^b) =~ Hom(b, a)
*)

Definition SProxy3 (a' a b' b : Type) (m : Type -> Type) (r : Type) : Type :=
     (a' -> a)            (* await *)
  -> (b  -> b')           (* yield *)
  -> (forall x, m x -> x) (* pure *)
  -> r.                   (* pure *)

(* We need to plumb through the monadic effects, and remove trivialities *)

Definition SProxy4 (a' a b' b : Type) (m : Type -> Type) (r : Type) : Type :=
     (a' -> m a)            (* await *)
  -> (b  -> m b')           (* yield *)
  -> m r.                   (* pure *)

(* And add the ability to terminate early *)

Definition SProxy4 (a' a b' b : Type) (m : Type -> Type) (r : Type) : Type :=
     (a' -> EitherT r m a)            (* await *)
  -> (b  -> EitherT r m b')           (* yield *)
  -> EitherT r m r.                   (* pure *)

End SProxy.

End PipesLaws.
