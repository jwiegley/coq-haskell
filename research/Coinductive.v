Require Import Hask.Prelude.

Generalizable All Variables.

Module Type Bisimulation.

Variables T C : Type.
Variable embed : T -> C.
Variable approx : nat -> C -> T.

Hypothesis approx_embed : forall x : T, exists m : nat, approx m (embed x) = x.

Hypothesis embed_approx : forall n (c : C),
  approx n c = approx n (embed (approx n c)).

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

Definition SProxy (a' a b' b : Type) (m : Type -> Type) (r : Type) : Type :=
  forall s : Type,
       (a' -> (a  -> s) -> s)           (* SRequest *)
    -> (b  -> (b' -> s) -> s)           (* SRespond *)
    -> (forall x, (x -> s) -> m x -> s) (* SM *)
    -> (r -> s)                         (* SPure *)
    -> s.

Definition toProxy `(s : SProxy a' a b' b m r) : Proxy a' a b' b m r :=
  s _ Request Respond (fun _ => M) Pure.

Fixpoint fromProxy `(p : Proxy a' a b' b m r) : SProxy a' a b' b m r :=
  fun _ req res mon k =>
    match p with
    | Request a' fa  => req a' (fun a  => fromProxy (fa  a)  _ req res mon k)
    | Respond b  fb' => res b  (fun b' => fromProxy (fb' b') _ req res mon k)
    | M _     g  h   => mon _  (fun x  => fromProxy (g x) _ req res mon k) h
    | Pure    x      => k x
    end.

CoInductive CoProxy (a' a b' b : Type) (m : Type -> Type) (r : Type) : Type :=
  | CoRequest of a' & (a  -> CoProxy a' a b' b m r)
  | CoRespond of b  & (b' -> CoProxy a' a b' b m r)
  | CoM : forall x, (x -> CoProxy a' a b' b m r) -> m x -> CoProxy a' a b' b m r
  | CoPure of r.

Arguments CoRequest {a' a b' b m r} _ _.
Arguments CoRespond {a' a b' b m r} _ _.
Arguments CoM {a' a b' b m r x} _ _.
Arguments CoPure {a' a b' b m r} _.

Definition stream `(co : Proxy a' a b' b m r) : CoProxy a' a b' b m r :=
  let cofix go p := match p with
    | Request a' fa => CoRequest a' (go \o fa)
    | Respond b  fb => CoRespond b  (go \o fb)
    | M _     f  t  => CoM (go \o f) t
    | Pure       a  => CoPure a
    end in
  go co.

(*
Definition render `(co : CoProxy a' a b' b m r) : Proxy a' a b' b m r :=
  let fix go p := match p with
    | CoRequest a' fa => Request a' (go \o fa)
    | CoRespond b  fb => Respond b  (go \o fb)
    | CoM _     f  t  => M (go \o f) t
    | CoPure       a  => Pure a
    end in
  go co.
*)

CoFixpoint push `{Monad m} {a' a r} : a -> CoProxy a' a a' a m r :=
  CoRespond ^~ (CoRequest ^~ push).

(*
Inductive pushR_ev {a' a b' b c' c m r}
  (p0 : CoProxy a' a b' b m r) (fb : b -> CoProxy b' b c' c m r) : Prop :=
  | ev_pushR_req : forall aa' fa, p0 = CoRequest aa' fa -> pushR_ev p0 fb
  | ev_pushR_res : forall bb  fb',
      p0 = CoRespond bb fb' -> pullR_ev fb' (fb bb) -> pushR_ev p0 fb

with pullR_ev {a' a b' b c' c m r}
  (fb' : b' -> Proxy a' a b' b m r) (p0 : Proxy b' b c' c m r) : Prop :=
  | ev_pullR_req : forall aa' fa, p0 = CoRequest aa' fa -> pullR_ev fb' p0.
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

CoFixpoint pull `{Monad m} {a' a r} : a' -> CoProxy a' a a' a m r :=
  CoRequest ^~ (CoRespond ^~ pull).

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

Axiom elim : forall `(f : a -> (b -> s) -> s) (x : a) (y : s),
  f x (const y) = y.

Axiom flip_elim : forall `(f : (b -> s) -> a -> s) (x : a) (y : s),
  f (const y) x = y.

(* Lemma foo : forall `(x : SProxy a' a b' b m r) (z : r) s req res mon k, *)
(*   x s req res mon k = k z -> toProxy x = Pure z. *)
(* Proof. *)
(*   move=> a' a b' b m r x z. *)
(*   rewrite /toProxy. *)

Lemma SProxy_from_to : forall `(x : SProxy a' a b' b m r),
  fromProxy (toProxy x) = x.
Proof.
  move=> a' a b' b m r x.
  extensionality s.
  extensionality req.
  extensionality res.
  extensionality mon.
  extensionality k.
  (* elim E: (toProxy x) => [? ? IHu|? ? IHu|? ? IHu| ?]. *)
  (* admit. admit. admit. *)
  (* rewrite /fromProxy /=. *)
  move: (toProxy x).
  reduce_proxy IHx
    (rewrite /fromProxy /=;
     try (move/functional_extensionality in IHx;
          try move=> m0;
          rewrite IHx ?elim ?flip_elim)).
Admitted.
