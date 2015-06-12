Require Import Hask.Prelude.

Generalizable All Variables.

Module Type Bisimulation.

Variables T C : Type.
Variable embed : T -> C.
Variable approx : nat -> C -> T.

Hypothesis approx_embed : forall x : T, exists m : nat, approx m (embed x) = x.

Lemma embed_approx : forall n (c : C),
  approx n c = approx n (embed (approx n c)).
Proof.
  move=> n c.
  destruct (approx_embed (approx n c)).
  rewrite -{1}H.
  f_equal.

Theorem approximately : forall (c : C) (P : C -> Prop) (n : nat) (t : T),
  t = approx n c -> P (embed t) -> P c.
Proof.
  move=> c ? n t Heqe H.
  rewrite Heqe in H.
  rewrite embed_approx in H.
  have H0 := approx_embed t.
  destruct H0.
  rewrite Heqe -(approx_inj n c (embed _)) // in H.
  exact: embed_approx.
Qed.

End Bisimulation.

Module Streams <: Bisimulation.

CoInductive stream (a : Type) :=
  | SNil : stream a
  | SCons : a -> stream a -> stream a.

Variable a : Type.

Definition T := seq a.
Definition C := stream a.

CoFixpoint embed_stream `(x : seq a) : stream a :=
  match x with
    | nil => SNil _
    | cons x xs => SCons _ x (embed_stream xs)
  end.

Fixpoint approx_stream (n : nat) `(x : stream a) : seq a :=
  if n isn't S n' then nil else
  match x with
  | SNil => nil
  | SCons x xs => cons x (approx_stream n' xs)
  end.

Definition embed := embed_stream.
Definition approx := approx_stream.

Lemma approx_embed : forall x : T, exists m : nat, approx m (embed x) = x.

Lemma embed_approx : forall n (c : C),
  approx n c = approx n (embed (approx n c)).

End Streams.

(*
Fixpoint pushR `{Monad m} {a' a b' b c' c r} (p0 : Proxy a' a b' b m r)
  (fb : b -> Proxy b' b c' c m r) {struct p0} : Proxy a' a c' c m r :=
  foldProxy (s:=Proxy a' a c' c m r)
    Request (flip pullR \o fb) (fun _ => M) Pure p0

with pullR `{Monad m} {a' a b' b c' c r} (fb' : b' -> Proxy a' a b' b m r)
  (p0 : Proxy b' b c' c m r) {struct p0} : Proxy a' a c' c m r :=
  foldProxy (s:=Proxy a' a c' c m r)
    (pushR \o fb') Respond (fun _ => M) Pure p0.

Fixpoint pushR `{Monad m} {a' a b' b c' c r} (p0 : Proxy a' a b' b m r)
  (fb : b -> Proxy b' b c' c m r) {struct p0} : Proxy a' a c' c m r :=
  let fix go p := match p with
    | Request a' fa  => Request a' (go \o fa)
    | Respond b  fb' => pullR (fb b) fb'
    | M _     f  t   => M (go \o f) t
    | Pure       a   => Pure a
    end in
  go p0

with pullR `{Monad m} {a' a b' b c' c r} (p0 : Proxy b' b c' c m r)
  (fb' : b' -> Proxy a' a b' b m r) {struct p0} : Proxy a' a c' c m r :=
  let fix go p := match p with
    | Request b' fb  => pushR (fb' b') fb
    | Respond c  fc' => Respond c (go \o fc')
    | M _     f  t   => M (go \o f) t
    | Pure       a   => Pure a
    end in
  go p0.
*)

CoInductive CoProxy (a' a b' b : Type) (m : Type -> Type) (r : Type) : Type :=
  | CoRequest of a' & (a  -> CoProxy a' a b' b m r)
  | CoRespond of b  & (b' -> CoProxy a' a b' b m r)
  | CoM : forall x, (x -> CoProxy a' a b' b m r) -> m x -> CoProxy a' a b' b m r
  | CoPure of r.

Arguments CoRequest {a' a b' b m r} _ _.
Arguments CoRespond {a' a b' b m r} _ _.
Arguments CoM {a' a b' b m r x} _ _.
Arguments CoPure {a' a b' b m r} _.

CoFixpoint push `{Monad m} {a' a r} : a -> CoProxy a' a a' a m r :=
  CoRespond ^~ (CoRequest ^~ push).

Fixpoint render (n : nat) `(dflt : r) `(co : CoProxy a' a b' b m r) :
  Proxy a' a b' b m r :=
  if n isn't S n' then Pure dflt else
  match co with
    | CoRequest a' fa => Request a' (render n' dflt \o fa)
    | CoRespond b  fb => Respond b  (render n' dflt \o fb)
    | CoM _     f  t  => M (render n' dflt \o f) t
    | CoPure       a  => Pure a
    end.

Definition stream `(co : Proxy a' a b' b m r) : CoProxy a' a b' b m r :=
  let cofix go p := match p with
    | Request a' fa => CoRequest a' (go \o fa)
    | Respond b  fb => CoRespond b  (go \o fb)
    | M _     f  t  => CoM (go \o f) t
    | Pure       a  => CoPure a
    end in
  go co.

Inductive pushR_ev {a' a b' b m r} : CoProxy a' a b' b m r -> Prop :=
  | ev_pushR_req  : forall aa' fa, pushR_ev (CoRequest aa' fa)
  | ev_pushR_res  : forall bb  fb fb',
      pullR_ev (fb' bb) -> pushR_ev (CoRespond bb fb)
  | ev_pushR_mon  : forall x g (h : m x), pushR_ev (CoM g h)
  | ev_pushR_pure : forall x : r, pushR_ev (CoPure x)

with pullR_ev {a' a b' b m r} : CoProxy a' a b' b m r -> Prop :=
  | ev_pullR_req  : forall aa' fa fa',
      pushR_ev (fa' aa') -> pullR_ev (CoRequest aa' fa)
  | ev_pullR_res  : forall bb  fb, pullR_ev (CoRequest bb fb)
  | ev_pullR_mon  : forall x g (h : m x), pullR_ev (CoM g h)
  | ev_pullR_pure : forall x : r, pullR_ev (CoPure x).

(*
Lemma eventually_pushR_inv {a' a b' b m r} : forall bb fb,
  @pushR_ev a' a b' b m r (CoRespond (bb : b) fb)
    -> forall x : b', pushR_ev (fb x).

Lemma eventually_pullR_inv {a' a b' b m r} : forall aa' fa,
  @pullR_ev a' a b' b m r (CoRequest (aa' : a') fa)
    -> forall x : a, pullR_ev (fa x).
*)

(*
Require Import Coq.Program.Equality.
Import EqNotations.

Fixpoint pre_pushR {a' a b' b m r} (x : CoProxy a' a b' b m r)
  (d : pushR_ev x) {struct d} :
  a' * CoProxy a' a b' b m r :=
  match x as z return x = z -> a' * CoProxy a' a b' b m r with
  | CoRequest a' fa  => fun heq => (a', ?)
  | CoRespond bb fb' => fun heq =>
      pre_pushR (fb' ?)
                (eventually_pushR_inv bb fb' d ?)
  | CoM _     f  t   => fun heq => ?
  | CoPure       a   => fun heq => ?
  end (refl_equal x).
*)

(*
CoFixpoint pushR `{Monad m} {a' a b' b c' c r} (p0 : CoProxy a' a b' b m r)
  (fb : b -> CoProxy b' b c' c m r) {struct p0} : CoProxy a' a c' c m r :=
  let cofix go p := match p with
    | CoRequest a' fa  => CoRequest a' (go \o fa)
    | CoRespond b  fb' =>
        let cofix go' p := match p with
          | CoRequest b' fb  => go (fb' b')
          | CoRespond c  fc' => CoRespond c (go' \o fc')
          | CoM _     f  t   => CoM (go' \o f) t
          | CoPure       a   => CoPure a
          end in
        go' (fb b)
    | CoM _     f  t   => CoM (go \o f) t
    | CoPure       a   => CoPure a
    end in
  go p0.
*)

(*
Program Instance Push_Category
  (n : nat) (_ : n > 0) {r} (dflt : r) `{MonadLaws m} :
  Category := {
  ob     := Type * Type;
  hom    := fun A B => snd A -> CoProxy (fst A) (snd A) (fst B) (snd B) m r;
  c_id   := fun A => @push m _ (fst A) (snd A) r;
  c_comp := fun _ _ _ f g => g >~> f
}.
Obligation 1. (* Right identity *)
  rewrite /stream /= in f *.
  case: n => // [n'] in H1 *.
  extensionality z => /=.
  move: (f z).
  destruct f0.
  simpl.
  reduce_proxy IHx idtac.
  f_equal.
  extensionality x.
  specialize (IHx x).
  rewrite -IHx.
  unfold funcomp in *. simpl in *.
  rewrite -IHx.
  rewrite /funcomp /=.
Obligation 2. (* Left identity *)
(* Obligation 3. (* Associativity *) *)
*)


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

(* Fixpoint push `{Monad m} {a' a r} {n : nat} {default : r} : *)
(*   a -> Proxy a' a a' a m r := *)
(*   if n isn't S n' then (fun _ => Pure default) else *)
(*   (Respond ^~ (Request ^~ @push _ _ _ _ _ n' default)). *)

