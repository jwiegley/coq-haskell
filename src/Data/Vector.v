Require Import Hask.Prelude.

Generalizable All Variables.

Section Vector.

Variable A : Type.

Definition Vec : nat -> Type :=
  fix vec n := match n return Type with
               | O   => unit
               | S n => prod A (vec n)
               end.

Definition vnil : Vec 0 := tt.

Definition vsing (x : A) : Vec 1 := (x, tt).

Definition vcons {n} (x : A) (v : Vec n) : Vec n.+1 := (x, v).

Definition fin_contra : forall {x}, 'I_0 -> x.
Proof. by move=> x; case=> m; move/eqP: (ltn0 m) => Hcontra //. Defined.

Definition fin_rect {n} : forall (P : 'I_n.+1 -> Type),
  (forall {H}, P (@Ordinal n.+1 0 H))
    -> (forall {m H}, P (@Ordinal n.+1 m (ltnW H))
          -> P (@Ordinal n.+1 m.+1 H))
    -> forall (x : 'I_n.+1), P x.
Proof.
  move=> P Hz HSn; case=> m H.
  elim: m => [|m IHm] in H *; [ exact: Hz | exact/HSn/IHm ].
Defined.

Definition vec_rect : forall (P : forall {n}, Vec n -> Type),
  P vnil
    -> (forall {n} (x : A) (v : Vec n), P v -> P (vcons x v))
    -> forall {n} (v : Vec n), P v.
Proof.
  move=> P Hnil Hcons n v.
  elim: n => [|n IHn] in Hnil Hcons v *.
    case: v; exact: Hnil.
  case: v => *; exact/Hcons/IHn.
Defined.

Definition vecn_rect : forall (P : forall {n}, Vec n -> Type),
  (forall x : A, P (vsing x))
    -> (forall {n} (x : A) (v : Vec n.+1), P v -> P (vcons x v))
    -> forall {n} (v : Vec n.+1), P v.
Proof.
  move=> P Hsing Hcons n v.
  elim: n => [|n IHn] in Hsing Hcons v *.
    case: v => a b; case: b; exact: Hsing.
  case: v => *; exact/Hcons/IHn.
Defined.

Definition vfoldl_with_index
  {B : Type} {n} (f : 'I_n -> B -> A -> B) (b : B) (v : Vec n) : B.
Proof.
  case: n => [//|n] in f v *.
  elim/vecn_rect: v => [x|sz x xs IHxs].
    exact: (f (inord n) b x).
  exact: (f (inord (n - sz.+1)) IHxs x).
Defined.

Definition vfoldl {B : Type} {n} (f : B -> A -> B) (b : B) (v : Vec n) : B :=
  vfoldl_with_index (fun _ => f) b v.

Definition vconst {n} (i : A) : Vec n.
Proof.
  elim: n => [|n IHn]; [ exact: vnil | exact: (vcons i IHn) ].
Defined.

Definition vreplace {n} (v : Vec n) (p : 'I_n) (i : A) : Vec n.
Proof.
  case: n => [|n] in v p *;
    first exact: fin_contra.
  elim/vecn_rect: v => [x|? x xs IHxs] in p *.
    exact: (vsing i).
  elim/@fin_rect: p => [_|p ? _].
    exact: (vcons i xs).
  exact: (vcons x (IHxs (@Ordinal _ p _))).
Defined.

Definition vnth {n} (v : Vec n) (p : 'I_n) : A.
Proof.
  case: n => [|n] in v p *;
    first exact: fin_contra.
  elim/vecn_rect: v => [x|? x _ IHxs] in p *; first exact: x.
  elim/@fin_rect: p => [_|p ? _]; first exact: x.
  exact: (IHxs (@Ordinal _ p _)).
Defined.

Definition vshiftin {n} (v : Vec n) (i : A) : Vec n.+1.
Proof.
  elim/vec_rect: v => [|? x ? IHxs]; [ exact: (vsing i) | exact: (x, IHxs) ].
Defined.

Definition vapp {n m} (v : Vec n) (u : Vec m) : Vec (n + m).
Proof.
  elim/vec_rect: v => [|? x _ IHxs]; [ exact: u | exact: (vcons x IHxs) ].
Defined.

Definition widen_id {n} := widen_ord (leqnSn n).

(* The following properties are all to support the [beginnings] Theorem at
   the end of Spec.v. *)

Definition fin_ind {n} : forall (P : 'I_n.+1 -> Prop),
  (forall {H}, P (@Ordinal n.+1 0 H))
    -> (forall {m H}, P (@Ordinal n.+1 m (ltnW H))
          -> P (@Ordinal n.+1 m.+1 H))
    -> forall (x : 'I_n.+1), P x := [eta fin_rect].

Definition vec_ind : forall (P : forall {n}, Vec n -> Prop),
  P vnil
    -> (forall {n} (x : A) (v : Vec n), P v -> P (vcons x v))
    -> forall {n} (v : Vec n), P v := [eta vec_rect].

Definition vecn_ind : forall (P : forall {n}, Vec n -> Prop),
  (forall x : A, P (vsing x))
    -> (forall {n} (x : A) (v : Vec n.+1), P v -> P (vcons x v))
    -> forall {n} (v : Vec n.+1), P v := [eta vecn_rect].

Lemma vnth_cons0 : forall n i (v : Vec n) H,
  vnth (vcons i v) (@Ordinal n.+1 0 H) = i.
Proof. by move=> n i; elim/vec_ind. Qed.

Lemma vnth_consn : forall n i (v : Vec n) m, forall H: m < n,
  vnth (vcons i v) (@Ordinal n.+1 m.+1 H) = vnth v (@Ordinal n m H).
Proof. by move=> n i; elim/vec_ind. Qed.

Lemma vshiftin_cons : forall n z (v : Vec n) i,
  vshiftin (vcons z v) i = vcons z (vshiftin v i).
Proof. by move=> n z; elim/vec_ind. Qed.

Lemma vnth_last : forall n (i : A) (v : Vec n),
  vnth (vshiftin v i) ord_max = i.
Proof.
  move=> n i.
  elim/vec_ind=> // [sz x xs IHxs].
  rewrite vshiftin_cons vnth_consn.
  have ->: Ordinal (n:=sz.+1) (m:=sz) (ltnSn sz.+1) = ord_max.
    congr (Ordinal _).
    exact: eq_irrelevance.
  exact: IHxs.
Qed.

Lemma vreplace_cons0 n (k : 'I_n.+1) : forall i (v : Vec n) z,
  k == ord0 -> vreplace (vcons i v) k z = vcons z v.
Proof.
  move=> i v z H.
  elim/vec_ind: v => [|? ? ? _] in k H *;
  by elim/@fin_ind: k => // in H *.
Qed.

Lemma vreplace_consn : forall n m i (v : Vec n) z, forall H: m < n,
  vreplace (vcons i v) (@Ordinal n.+1 m.+1 H) z
    = vcons i (vreplace v (@Ordinal n m H) z).
Proof. by move=> n m i; elim/vec_ind. Qed.

Lemma vnth_vreplace : forall n (v : Vec n) k z,
  vnth (vreplace v k z) k = z.
Proof.
  move=> n v k z.
  case: n => [|n] in k v *;
    first exact: fin_contra.
  elim/vecn_ind: v => // [sz x xs IHxs] in k *.
  elim/@fin_ind: k => [H|k ? IHk].
    rewrite vreplace_cons0; last by [].
    by rewrite vnth_cons0.
  by rewrite vreplace_consn vnth_consn IHxs.
Qed.

Lemma fin1_eq : forall (j k : 'I_1), j == k.
Proof.
  elim/@fin_ind=> [?|? ? _];
  elim/@fin_ind=> [?|? ? _]; first by [];
  discriminate.
Qed.

Lemma vnth_vreplace_neq : forall n (v : Vec n) (k j : 'I_n) (z : A),
  k != j -> vnth (vreplace v k z) j = vnth v j.
Proof.
  move=> n v k j z.
  case: n => [|n] in k j v *;
    first exact: fin_contra.
  elim/vecn_ind: v => // [x|sz x xs IHxs] in k j *.
    by move: (fin1_eq k j) => /eqP ? /eqP ?.
  elim/@fin_ind: k; elim/@fin_ind: j;
    try by elim: sz => // in xs IHxs *.
  move=> ? ? _ ? ? _ Hneg.
  rewrite vreplace_consn !vnth_consn IHxs; first by [].
  exact: Hneg.
Qed.

Definition vnth_vshiftin {n} : forall k (z : A) (v : Vec n),
  vnth (vshiftin v z) (widen_id k) = vnth v k.
Proof.
  move=> k z v.
  case: n => [|n] in k v *;
    first exact: fin_contra.
  elim/vecn_ind: v => [x|sz x xs IHxs] in k *.
    rewrite /vshiftin /=.
    by elim/@fin_ind: k => //.
  rewrite vshiftin_cons.
  elim/@fin_ind: k => [Hk|? ? _].
    have ->: Hk = ltn0Sn sz by exact: eq_irrelevance.
    by rewrite vnth_cons0.
  rewrite !vnth_consn -IHxs.
  congr (vnth _ (Ordinal _)).
  exact: eq_irrelevance.
Qed.

Definition vec_to_seq `(v : Vec n) : seq A.
Proof.
  case: n => [|n] in v *.
    exact: [::].
  elim/vecn_rect: v => [x|sz x ? IHxs].
    exact: [:: x].
  exact: (x :: IHxs).
Defined.

Lemma vec_seq_cons (x : A) `(xs : Vec n) :
  vec_to_seq (vcons x xs) = x :: vec_to_seq xs.
Proof.
  case: n => [|n] in xs *.
    by case: xs.
  by elim/vecn_rect: xs.
Qed.

Lemma vec_to_seq_size `(v : Vec n) : size (vec_to_seq v) == n.
Proof.
  case: n => // [n] in v *.
  by elim/vecn_rect: v.
Defined.

Definition seq_to_vec (l : seq A) : Vec (size l).
Proof. by elim: l. Defined.

Theorem vec_seq (xs : seq A) : vec_to_seq (seq_to_vec xs) = xs.
Proof.
  elim: xs => // [x xs IHxs].
  by rewrite [seq_to_vec _]/= vec_seq_cons IHxs.
Qed.

(* Import EqNotations. *)
(* Require Import ProofIrrelevance. *)

(* Theorem seq_vec `(v : Vec n) : *)
(*   rew (eqP (vec_to_seq_size _)) in seq_to_vec (vec_to_seq v) = v. *)
(* Proof. *)
(*   case: n => [|n] in v *. *)
(*     case: v. *)
(*     by rewrite -eq_rect_eq. *)
(*   elim/vecn_rect: v => [x|sz x xs IHxs]. *)
(*     by rewrite -eq_rect_eq. *)

End Vector.

Definition vmap {A B : Type} {n} (f : A -> B) (v : Vec A n) : Vec B n.
Proof.
  elim: n => // [n IHn] in v *.
  elim/vecn_rect: v => [x|sz x ? IHxs].
    exact: (vsing _ (f x)).
  exact: (vcons _ (f x) IHxs).
Defined.

Module VectorSpec.

Arguments vsing [A] _ /.
Arguments vcons [A n] _ _ /.
Arguments vconst [A n] !i.
Arguments vfoldl_with_index [A B n] f !b !v.
Arguments vfoldl [A B n] f !b !v.
Arguments vreplace [A n] !v !p !i.
Arguments vnth [A n] !v !p.
Arguments vapp [A n m] !v !u.
Arguments vshiftin [A n] !v !i.
Arguments vmap [A B n] f !v.
Arguments vec_to_seq [A n] !v.
Arguments seq_to_vec [A] !l.

Example flwi_check :
  map (fun x => (@nat_of_ord 5 (fst x), (snd x)))
      (vfoldl_with_index (fun i acc x => (i, x) :: acc) nil
         (vcons 1 (vcons 2 (vcons 3 (vcons 4 (vsing 5))))))
    == [:: (0, 1); (1, 2); (2, 3); (3, 4); (4, 5)].
Proof. rewrite /= !inordK; by []. Qed.

Lemma _2_ltn_5 : 2 < 5. Proof. by []. Qed.

Example vreplace_check :
  vreplace (vcons 1 (vcons 2 (vcons 3 (vcons 4 (vsing 5)))))
          (@Ordinal 5 2 _2_ltn_5) 6
    == (vcons 1 (vcons 2 (vcons 6 (vcons 4 (vsing 5))))).
Proof. reflexivity. Qed.

Lemma _3_ltn_5 : 3 < 5. Proof. by []. Defined.

Example vnth_check :
  vnth (vcons 1 (vcons 2 (vcons 3 (vcons 4 (vsing 5)))))
       (@Ordinal 5 3 _3_ltn_5) == 4.
Proof. reflexivity. Qed.

Example vapp_check :
  vapp (vcons 1 (vsing 2))
       (vcons 3 (vcons 4 (vsing 5))) ==
  vcons 1 (vcons 2 (vcons 3 (vcons 4 (vsing 5)))).
Proof. reflexivity. Qed.

Example const_check :
  vconst 42 = vcons 42 (vcons 42 (vcons 42 (vcons 42 (vsing 42)))).
Proof. reflexivity. Qed.

Example vmap_check :
  vmap (addn 2) (vcons 1 (vcons 2 (vcons 3 (vcons 4 (vsing 5)))))
    == (vcons 3 (vcons 4 (vcons 5 (vcons 6 (vsing 7))))).
Proof. reflexivity. Qed.

End VectorSpec.
