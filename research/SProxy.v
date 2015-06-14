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

End SProxy.
