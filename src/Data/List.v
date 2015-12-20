Require Import Hask.Ssr.
Require Import Hask.Ltac.
Require Import Hask.Control.Monad.

Require Import Coq.Program.Wf.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Classes.RelationClasses.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition concat {A} : seq (seq A) -> seq A := flatten.

Fixpoint lookup {a : eqType} {b} (dflt : b) (v : seq (a * b)) (x : a) : b :=
  if v is (k, v) :: xs
  then if k == x
       then v
       else lookup dflt xs x
  else dflt.

Fixpoint maybeLookup {a : eqType} {b} (v : seq (a * b)) (x : a) : option b :=
  if v is (k, v) :: xs
  then if k == x
       then Some v
       else maybeLookup xs x
  else None.

Fixpoint valueLookup {a} {b : eqType} (dflt : a)
  (v : seq (a * b)) (x : b) : a :=
  if v is (k, v) :: xs
  then if v == x
       then k
       else valueLookup dflt xs x
  else dflt.

Fixpoint maybeValueLookup {a} {b : eqType} (v : seq (a * b)) (x : b) :
  option a :=
  if v is (k, v) :: xs
  then if v == x
       then Some k
       else maybeValueLookup xs x
  else None.

Definition listToMaybe `(xs : seq a) : option (seq a) :=
  if xs is [::]
  then None
  else Some xs.

Definition maybeToList `(mx : option a) : seq a :=
  match mx with
  | Some x => [:: x]
  | None   => [::]
  end.

Lemma rcons_nil : forall a us (u : a), rcons us u = [::] -> False.
Proof. by move=> a us u; case: us => // [|? ?] in u *. Qed.

Definition olast a (l : seq a) : option a :=
  let fix go res xs :=
      match xs with
      | nil => res
      | cons x xs => go (Some x) xs
      end in
  go None l.

Example olast_ex1 : olast ([::] : seq nat) == None.
Proof. by []. Qed.

Example olast_ex2 : olast [:: 1] == Some 1.
Proof. by []. Qed.

Example olast_ex3 : olast [:: 1; 2; 3] == Some 3.
Proof. by []. Qed.

Lemma olast_last : forall a (u : a) us,
  olast (u :: us) = Some (last u us).
Proof.
  move=> a u.
  elim=> //= [x xs IHxs].
  case: xs => //= [|y ys] in IHxs *.
Qed.

Lemma olast_spec : forall a (u : a) us, olast (u :: us) = None -> False.
Proof.
  move=> a u.
  elim=> //= [x xs IHxs] H.
  rewrite olast_last /= in H.
  rewrite olast_last in IHxs.
  case: xs => //= [|y ys] in H IHxs *.
Qed.

Lemma olast_rcons : forall a (u : a) us, olast (rcons us u) = Some u.
Proof.
  move=> a u.
  elim=> //= [x xs IHxs].
  case: xs => // [|y ys] in IHxs *.
Qed.

Lemma olast_cons : forall a (x y : a) ys,
  olast (x :: y :: ys) = olast (y :: ys).
Proof.
  move=> a x y.
  elim=> //= [x xs IHxs].
Qed.

Lemma olast_cons_rcons : forall a (z u : a) us,
  olast (z :: rcons us u) = Some u.
Proof.
  move=> a z u.
  elim=> //= [x xs IHxs].
  case: xs => // [|y ys] in IHxs *.
Qed.

Lemma olast_cat : forall a (x : a) xs ys,
  olast (ys ++ x :: xs) = olast (x :: xs).
Proof.
  move=> a y xs ys.
  elim: xs => /= [|z zs IHzs] in y ys *.
    by rewrite cats1 olast_rcons.
  replace [:: y, z & zs] with ([:: y] ++ [:: z & zs]).
    by rewrite catA !IHzs.
  by [].
Qed.

Lemma olast_cat_rcons : forall a (x : a) xs ys,
  olast (ys ++ rcons xs x) = Some x.
Proof.
  move=> a y xs ys.
  elim: xs => /= [|z zs IHzs] in y ys *.
    by rewrite cats1 olast_rcons.
  rewrite olast_cat -cat1s.
  exact: IHzs.
Qed.

Definition oends a (l : seq a) : option (a + (a * a)).
Proof.
  case: l => [|x xs].
    exact: None.
  case/lastP: xs => [|ys y].
    exact: Some (inl x).
  exact: Some (inr (x, y)).
Defined.

Lemma oends_spec a (l : seq a) :
  match oends l with
  | Some (inr (x, y)) => head x l = x /\ last y l = y
  | Some (inl x)      => head x l = last x l
  | None              => True
  end.
Proof.
  rewrite /oends.
  case: l => // [x xs].
  case/lastP: xs => //= [ys y].
  by rewrite last_rcons.
Qed.

Lemma last_leq : forall (z y : nat) (xs : seq nat) (n : nat),
  last z xs <= n -> y <= z -> last y xs <= n.
Proof.
  move=> z y.
  elim=> //= [x xs IHxs].
  exact: leq_trans IHxs _.
Qed.

Lemma last_leq_ltn : forall (z y : nat) (xs : seq nat) (n : nat),
  last z xs < n -> y <= z -> last y xs < n.
Proof.
  move=> z y.
  elim=> //= [x xs IHxs].
  exact: leq_ltn_trans IHxs _.
Qed.

Lemma last_ltn : forall (z y : nat) (xs : seq nat) (n : nat),
  last z xs < n -> y <= z -> last y xs < n.
Proof.
  move=> z y.
  elim=> //= [x xs IHxs].
  exact: leq_ltn_trans IHxs _.
Qed.

Lemma list_cons_nonzero : forall {a x} {xs l : seq a},
  l = x :: xs -> size l > 0.
Proof. by move=> a x xs l ->. Qed.

Definition exist_in_cons : forall {A : eqType} {a} {l : seq A},
  {x : A | x \in l} -> {x : A | x \in a :: l}.
Proof.
  move=> A a l.
  case=> x H.
  exists x.
  rewrite in_cons.
  by apply/orP; right.
Defined.

Definition list_membership {a : eqType} (l : seq a) :
  seq { x : a | x \in l } :=
  let fix go l :=
      match l with
      | nil => nil
      | cons x xs =>
          exist _ x (mem_head _ xs) :: map exist_in_cons (go xs)
      end in
  go l.

Fixpoint init {a : Type} (x : a) (l : seq a) :=
  match l with
    | nil => nil
    | cons y nil => [:: x]
    | cons y ys => x :: init y ys
  end.

Lemma Forall_head : forall A P (x : A) xs,
  List.Forall P (x :: xs) -> P (head x xs).
Proof.
  move=> A P x.
  elim=> /= [|y ys IHys] H.
    by inv H.
  by inv H; inv H3.
Qed.

Lemma Forall_rcons_inv : forall a P (x : a) xs,
  List.Forall P (rcons xs x) -> List.Forall P xs /\ P x.
Proof.
  move=> a P x.
  elim=> [|y ys IHys] /=.
    by invert.
  invert.
  specialize (IHys H2).
  inversion IHys.
  split=> //.
  constructor=> //.
Qed.

Lemma Forall_last : forall A P (x : A) xs,
  List.Forall P (x :: xs) -> P (last x xs).
Proof.
  move=> A P x.
  elim/last_ind=> /= [|ys y IHys] H.
    by inv H.
  inv H.
  rewrite last_rcons.
  apply Forall_rcons_inv in H3.
  by inv H3.
Qed.

Lemma Forall_append : forall A (P : A -> Prop) xs ys,
   List.Forall P xs /\ List.Forall P ys <-> List.Forall P (xs ++ ys).
Proof.
  move=> A P.
  elim=> [|x xs IHxs] /= ys.
    split.
      by move=> [H1 H2] //=.
    move=> H.
    split=> //.
  split.
    move=> [H1 H2] //=.
    constructor.
      by inversion H1.
    apply/IHxs.
    split=> //.
    by inversion H1.
  move=> H.
  split=> //.
    constructor.
      by inversion H.
    inversion H; subst.
    by move/IHxs: H3 => [? ?].
  inversion H; subst.
  by move/IHxs: H3 => [? ?].
Qed.

Lemma StronglySorted_inv_app : forall a R (l1 l2 : seq a),
  StronglySorted R (l1 ++ l2)
    -> StronglySorted R l1 /\ StronglySorted R l2.
Proof.
  move=> a R.
  elim=> [|x xs IHxs] /= l2 H.
    split=> //.
    constructor.
  inversion H.
  specialize (IHxs l2 H2).
  inversion IHxs; subst.
  split=> //.
  constructor=> //.
  by move/Forall_append: H3 => [? ?].
Qed.

Lemma StronglySorted_skip : forall a R (y : a) a0 ys,
  StronglySorted R [:: y, a0 & ys] -> StronglySorted R (y :: ys).
Proof.
  move=> a R y a0 ys H.
  elim: ys => [|z zs IHzs] in H *.
    by constructor; constructor.
  constructor.
    by constructor; inv H; inv H2; inv H1.
  by inv H; inv H3.
Qed.

Lemma StronglySorted_cat {A : Type} {xs ys : seq A} {R : A -> A -> Prop}
  `{Transitive _ R} :
  StronglySorted R xs -> StronglySorted R ys
    -> (match olast xs, ys with
        | Some x, y :: _ => R x y
        | _, _ => True
        end)
    -> StronglySorted R (xs ++ ys)%SEQ.
Proof.
  move=> Hsort1 Hsort2 Hrel.
  case/lastP: xs => //= [xs1 x1] in Hsort1 Hrel *.
  rewrite olast_rcons in Hrel.
  case: ys => [|y1 ys1] in Hsort2 Hrel *.
    by rewrite cats0.
  elim: xs1 => //= [|x2 xs2 IHxs2] in Hsort1 *.
    repeat constructor=> //.
    inv Hsort2.
    have: forall a : A, R y1 a -> R x1 a.
      move=> a Ha.
      exact: transitivity Hrel Ha.
    move/List.Forall_impl.
    exact.
  inv Hsort1.
  specialize (IHxs2 H2).
  constructor=> {H2} //.
  apply Forall_append.
  split=> //.
  apply Forall_rcons_inv in H3.
  move: H3 => [_ H3].
  constructor.
    exact: transitivity H3 Hrel.
  move/StronglySorted_inv_app: IHxs2 => [_ IHxs2].
  inv IHxs2.
  have: forall a : A, R y1 a -> R x2 a.
    move=> a Ha.
    exact: transitivity (transitivity H3 Hrel) Ha.
  move/List.Forall_impl.
  exact.
Qed.

Lemma StronglySorted_cat_cons
  {A : Type} {x y : A} {xs ys : seq A} {R : A -> A -> Prop} `{Transitive _ R} :
  StronglySorted R (x :: xs) -> StronglySorted R (y :: ys)
    -> R (last x xs) y
    -> StronglySorted R (x :: xs ++ y :: ys).
Proof.
  move=> Hsort1 Hsort2 Hrel.
  case/lastP: xs => /= [|xs1 x1] in Hsort1 Hrel *.
    constructor=> //.
    constructor=> //.
    inv Hsort2.
    have: forall a : A, R y a -> R x a.
      move=> a Ha.
      exact: transitivity Hrel Ha.
    move/List.Forall_impl.
    exact.
  rewrite -cat_cons.
  apply: StronglySorted_cat => //.
  rewrite olast_cons_rcons.
  by rewrite last_rcons in Hrel.
Qed.

Lemma StronglySorted_cons_cons : forall a (R : a -> a -> Prop) x xs y ys,
  StronglySorted R (x :: xs ++ y :: ys) -> R x y.
Proof.
  move=> a R x xs y ys H.
  elim: xs => [|z zs IHzs] /= in x y ys H *.
    by inv H; inv H3.
  apply: (IHzs x y ys).
  inv H.
  have H4 := H2.
  rewrite -cat_cons in H4.
  apply StronglySorted_inv_app in H4.
  inv H4.
  inv H2.
  constructor=> //.
  by inv H3.
Qed.

Lemma StronglySorted_rcons_inv : forall a R (x : a) xs,
  StronglySorted R (rcons xs x) -> StronglySorted R xs.
Proof.
  move=> a R x.
  elim=> [|y ys IHys] /=.
    by invert.
  invert.
  specialize (IHys H1).
  constructor=> //.
  apply Forall_rcons_inv in H2.
  by inversion H2.
Qed.

Lemma Forall_rcons_rcons : forall a R `{Transitive _ R} (x : a) y z xs,
  List.Forall (R z) (rcons xs x) -> R x y
    -> List.Forall (R z) (rcons (rcons xs x) y).
Proof.
  move=> a R H x y z.
  elim=> [|w ws IHws] /=.
    constructor.
      by inv H0.
    constructor.
      inv H0.
      exact: transitivity H4 H1.
    by constructor.
  constructor.
    by inv H0.
  apply: IHws => //.
  by inv H0.
Qed.

Lemma Forall_ordered : forall a (R : a -> a -> Prop) `{Transitive _ R} x y xs,
  R x y -> List.Forall (R y) xs -> List.Forall (R x) xs.
Proof.
  move=> a R H x y xs H1 H2.
  have: forall a, R y a -> R x a.
    move=> z H3.
    exact: transitivity H1 H3.
  move/List.Forall_impl.
  exact.
Qed.

Lemma StronglySorted_rcons_rcons : forall a R `{Transitive _ R} (x : a) y xs,
  StronglySorted R (rcons xs x) -> R x y
    -> StronglySorted R (rcons (rcons xs x) y).
Proof.
  move=> a R H x y.
  elim=> [|z zs IHzs] /=.
    by repeat constructor.
  constructor.
    inv H0.
   exact: (IHzs H4).
 inv H0.
 exact: Forall_rcons_rcons.
Qed.

Lemma StronglySorted_rcons_rcons_inv : forall a R (x y : a) xs,
  StronglySorted R (rcons (rcons xs x) y) -> R x y.
Proof.
  move=> a R x y.
  elim=> [|z zs IHzs] /=.
    invert.
    by inv H2.
  invert.
  exact: IHzs H1.
Qed.

Fixpoint maybe_nth {a} (v : seq a) i {struct i} :=
  match v with
  | [::] => None
  | x :: s' =>
      match i with
      | 0 => Some x
      | n'.+1 => maybe_nth s' n'
      end
  end.

Fixpoint apply_nth {a} (def : a) (v : seq a) i (f : a -> a) {struct i} :=
  if v is x :: v'
  then if i is i'.+1
       then x :: apply_nth def v' i' f
       else f x :: v'
  else ncons i def [:: def].

Definition forFold {A B : Type} (b : B) (v : seq A) (f : B -> A -> B) : B :=
  foldl f b v.

Definition forFoldr {A B : Type} (b : B) (v : seq A) (f : A -> B -> B) : B :=
  foldr f b v.

Definition foldl_with_index
  {A B : Type} (f : nat -> B -> A -> B) (b : B) (v : seq A) : B :=
  let fix go n xs z :=
      match xs with
        | nil => z
        | y :: ys => go n.+1 ys (f n z y)
      end in
  go 0 v b.

Example ex_foldl_with_index_1 :
  foldl_with_index (fun n z x => (n, x) :: z) nil [:: 1; 2; 3]
    == [:: (2, 3); (1, 2); (0, 1)].
Proof. reflexivity. Qed.

Lemma foldl_cons : forall a (x : a) xs,
  foldl (fun us : seq a => cons^~ us) [:: x] xs
    = foldl (fun us : seq a => cons^~ us) [::] [:: x & xs].
Proof. by move=> a x; elim. Qed.

Definition foldr_with_index
  {A B : Type} (f : nat -> A -> B -> B) (b : B) (v : seq A) : B :=
  let fix go n xs z :=
      match xs with
        | nil => z
        | y :: ys => f n y (go n.+1 ys z)
      end in
  go 0 v b.

Example ex_foldr_with_index_1 :
  foldr_with_index (fun n x z => (n, x) :: z) nil [:: 1; 2; 3]
    == [:: (0, 1); (1, 2); (2, 3)].
Proof. reflexivity. Qed.

Definition catMaybes {a} (l : seq (option a)) : seq a :=
  (fun f => foldr f [::] l) (fun mx rest =>
    if mx is Some x
    then x :: rest
    else rest).

Fixpoint mapAccumL {A X Y : Type} (f : A -> X -> (A * Y))
  (s : A) (v : seq X) : A * seq Y :=
  match v with
  | nil => (s, nil)
  | x :: xs =>
    let: (s', y) := f s x in
    let: (s'', ys) := mapAccumL f s' xs in
    (s'', y :: ys)
  end.

Example ex_mapAccumL_1 :
  mapAccumL (fun n x => (n.+1, x.+2)) 0 [:: 1; 2; 3] == (3, [:: 3; 4; 5]).
Proof. reflexivity. Qed.

Definition getBy {a} (p : a -> bool) (xs : seq a) : option a :=
  (fun f => foldl f None xs) (fun acc x =>
    match acc with
    | Some y => Some y
    | None =>
      if p x
      then Some x
      else None
    end).

Definition sumlist : seq nat -> nat := foldl addn 0.

Definition safe_nth {a} (xs : seq a) (n : nat) (H : n < size xs) : a.
Proof.
  elim: xs => [|x xs IHxs] in n H *.
    by [].
  elim: n => [|n IHn] in IHxs H *.
    exact: x.
  simpl in H.
  apply: IHn.
    move=> n0 H0.
    apply: IHxs.
    exact: H0.
  by ordered.
Defined.

Definition safe_hd {a} (xs : seq a) : 0 < size xs -> a.
Proof. case: xs => //. Defined.

Arguments safe_hd [a] xs H.

Definition safe_last {a} (xs : seq a) : 0 < size xs -> a.
Proof.
  case: xs => [//|y ys] /= *.
  exact: (last y ys).
Defined.

Arguments safe_last [a] xs H.

Fixpoint span {a} (p : a -> bool) (l : seq a) : (seq a * seq a) :=
  match l with
  | nil => (nil, nil)
  | x :: xs =>
    if p x
    then let: (ys,zs) := span p xs in (x::ys,zs)
    else (nil,l)
  end.

Lemma span_cat {a} (l : seq a) : forall p l1 l2,
  (l1, l2) = span p l
    -> l = l1 ++ l2 /\ all p l1 /\ (if l2 is x :: _ then ~~ (p x) else True).
Proof.
  move=> p.
  elim: l => /= [|x xs IHxs] l1 l2 Heqe.
    by inv Heqe.
  case E: (p x); rewrite E in Heqe.
    case S: (span p xs) => [l l0] in IHxs Heqe *.
    inv Heqe.
    move: (IHxs l l0 (refl_equal _)) => [? [? ?]].
    split; first by congr (_ :: _).
    split=> //.
    by apply/andP; split=> //.
  inv Heqe.
  split=> //.
  split=> //.
  by apply/negbT.
Qed.

Example span_ex1 :
  span (fun x => x < 10) [:: 1; 5; 10; 15] = ([:: 1; 5], [:: 10; 15]).
Proof. reflexivity. Qed.

Program Fixpoint groupBy {a} (p : a -> a -> bool) (l : seq a)
  {measure (size l)} : seq (seq a) :=
  match l with
  | [::] => nil
  | x :: xs => let: (ys, zs) := span (p x) xs in
               (x :: ys) :: groupBy p zs
  end.
Obligation 1.
  clear groupBy.
  rename Heq_anonymous into Heqe.
  move: ys zs Heqe.
  elim: xs => [|w ws /= IHws] ys zs /=.
    by invert.
  case: (p x w) => /=; last by invert.
  case: (span (p x) ws) => [bs cs] in IHws *.
  invert; subst.
  specialize (IHws bs cs refl_equal).
  move/ltP in IHws.
  apply/ltP.
  exact/leqW.
Qed.

Example groupBy_ex1 :
  groupBy eq_op [:: 1; 3; 3; 4; 5; 5; 9; 6; 8]
    = [:: [:: 1]; [:: 3; 3]; [:: 4]; [:: 5; 5]; [:: 9]; [:: 6]; [:: 8]].
Proof. reflexivity. Qed.

Definition partition {a} (p : a -> bool) : seq a -> seq a * seq a :=
  foldr (fun x acc =>
           if p x
           then (x :: fst acc, snd acc)
           else (fst acc, x :: snd acc)) ([::], [::]).

Lemma partition_all {a} {p q : a -> bool} (xs : seq a) :
  all p xs -> let: (ys, zs) := partition q xs in
              all (fun x => p x && q x) ys &&
              all (fun x => p x && ~~ q x) zs.
Proof.
  move=> H.
  elim: xs => //= [x xs IHxs] in H *.
  case: (partition q xs) => [ys zs] /= in IHxs *.
  move/andP: H => [H1 H2].
  specialize (IHxs H2).
  case E: (q x) => /=.
    by ordered.
  move/negbT in E.
  by ordered.
Qed.

Lemma perm_eq_nil : forall (a : eqType) (xs : seq a),
  perm_eq [::] xs -> xs = [::].
Proof.
  move=> a.
  elim=> //= [x xs IHxs].
  rewrite /perm_eq /=.
  move/andP => [H1 H2].
  rewrite eq_refl /= in H1.
  discriminate H1.
Qed.

Lemma all_perm : forall (a : eqType) (xs ys : seq a),
  perm_eq xs ys -> all^~ xs =1 all^~ ys.
Proof.
  move=> a xs ys H P.
  move/perm_eq_mem in H.
  by rewrite (eq_all_r H).
Qed.

Lemma all_catC {a} (P : pred a) (xs ys : seq a) :
  all P (xs ++ ys) = all P (ys ++ xs).
Proof.
  case: xs => /= [|x xs] in ys *.
    by rewrite cats0.
  case: ys => // [|y ys].
    by rewrite cats0.
  by rewrite !all_cat /= andbA andbC.
Qed.

Lemma all_flip : forall A (P : rel A) (_ : symmetric P) x (xs : seq A),
  all (P x) xs = all (P ^~ x) xs.
Proof.
  move=> A P H x.
  elim=> //= [y ys IHys].
  by rewrite -IHys H.
Qed.

Lemma all_all_cons : forall a (xs ys : seq a) (x : a) (R : rel a),
  all (fun y : a => all (R y) (x :: xs)) ys =
  all (R ^~ x) ys && all (fun y : a => all (R y) xs) ys.
Proof.
  move=> a xs ys x R.
  elim: ys => // [y ys IHys].
  rewrite [all]lock -{1}lock /= -lock IHys /= -!andbA.
  congr (_ && _).
  by rewrite and_swap.
Qed.

Lemma all_all_cat : forall A (P : rel A) (xs ys zs : seq A),
  all (fun x => all (P x) (xs ++ ys)) zs
    = all (fun x => all (P x) xs) zs && all (fun x => all (P x) ys) zs.
Proof.
  move=> A P xs ys.
  elim=> //= [z zs IHzs].
  rewrite IHzs all_cat.
  rewrite !andbA.
  congr (_ && _).
  rewrite -!andbA.
  congr (_ && _).
  by rewrite andbC.
Qed.

Lemma all_all_flip : forall A (P : rel A) (_ : symmetric P) (xs ys : seq A),
  all (fun x => all (P x) ys) xs = all (fun x => all (P ^~ x) ys) xs.
Proof.
  move=> A P H.
  elim=> //= [z zs IHzs] ys.
  by rewrite -IHzs all_flip.
Qed.

Lemma perm_cat_cons (T : eqType) (x : T) : forall (s1 s2 : seq_predType T),
  perm_eql (x :: s1 ++ s2) (s1 ++ x :: s2).
Proof.
  move=> s1 s2.
  apply/perm_eqlP.
  rewrite perm_eq_sym perm_catC cat_cons perm_cons perm_catC.
  exact: perm_eq_refl.
Qed.

Lemma perm_rem_cons (T : eqType) (x : T) : forall (s1 s2 : seq_predType T),
  x \in s1 -> perm_eql (rem x s1 ++ x :: s2) (s1 ++ s2).
Proof.
  move=> s1 s2 Hin.
  apply/perm_eqlP.
  rewrite perm_catC cat_cons perm_cat_cons perm_catC perm_cat2r perm_eq_sym.
  exact: perm_to_rem.
Qed.

Definition map_fst_filter_snd :
  forall (a b : eqType) (i : b) (xs : seq (a * b)),
  all (fun x => (x, i) \in xs) [seq fst x | x <- xs & snd x == i].
Proof.
  move=> a b i xs.
  apply/allP => x /mapP[[x1 y1]].
  by rewrite mem_filter => /= /andP [/eqP/=-> pIxs ->].
Qed.

Lemma has_size : forall (a : eqType) x (xs : seq a), x \in xs -> 0 < size xs.
Proof. move=> a x; elim=> //. Qed.

Fixpoint insert {a} (P : a -> a -> bool) (z : a) (l : seq a) : seq a :=
  if l is x :: xs
  then if P x z
       then x :: insert P z xs
       else z :: x :: xs
  else [:: z].
Arguments insert {a} P z l : simpl never.

Fixpoint sortBy {a} (p : a -> a -> bool) (l : seq a) : seq a :=
  match l with
  | [::] => nil
  | x :: xs => insert p x (sortBy p xs)
  end.

Example sortBy_ex1 :
  sortBy ltn [:: 1; 3; 5; 7; 9; 2; 4; 6; 8] = [:: 1; 2; 3; 4; 5; 6; 7; 8; 9].
Proof. reflexivity. Qed.

Example sortBy_ex2 :
  sortBy gtn [:: 1; 3; 5; 7; 9; 2; 4; 6; 8] = [:: 9; 8; 7; 6; 5; 4; 3; 2; 1].
Proof. reflexivity. Qed.

Example sortBy_ex3 :
  sortBy (fun x y => false) [:: 1; 3; 5; 7; 9; 2; 4; 6; 8] =
                            [:: 1; 3; 5; 7; 9; 2; 4; 6; 8].
Proof. reflexivity. Qed.

Lemma Forall_insert : forall a (R : a -> a -> bool) `{Transitive _ R} x xs y,
  R x y -> List.Forall (R x) xs -> List.Forall (R x) (insert R y xs).
Proof.
  move=> a R H x xs y H1 H2.
  elim: xs => [|z zs IHzs] /= in H1 H2 *.
    rewrite /insert.
    by constructor.
  rewrite /insert /= -/insert.
  case E: (R z y).
    constructor.
      by inv H2.
    apply: IHzs => //.
    by inv H2.
  constructor=> //.
Qed.

Lemma StronglySorted_insert :
  forall a (R : a -> a -> bool) `{Transitive _ R} x xs,
  StronglySorted R xs -> (forall y, ~~ R y x -> R x y)
    -> StronglySorted R (insert R x xs).
Proof.
  move=> a R H x xs H1 H2.
  elim=> [|y ys IHys] /= in H1 *.
    rewrite /insert.
    by constructor; constructor.
  rewrite /insert /= -/insert.
  case E: (R y x).
    constructor=> //.
    exact: Forall_insert.
  constructor.
    constructor=> //.
    constructor.
    apply/H2.
    by rewrite E.
  move/negbT/H2 in E.
  exact: (@Forall_ordered _ R H x y ys E H1).
Qed.

Lemma StronglySorted_impl_cons : forall a (R : a -> a -> bool) `{Transitive _ R}
  x y (ys : seq a), StronglySorted R (x :: y :: ys) -> R x (last y ys).
Proof.
  move=> a R H x y ys Hsort.
  elim: ys => [|z zs IHzs] /= in x y Hsort *.
    by inv Hsort; inv H3.
  apply: IHzs.
  inv Hsort; inv H2; inv H4.
  constructor=> //.
    constructor=> //.
  inv H3; inv H5.
  constructor=> //.
    by transitivity y.
  exact: (Forall_ordered H4).
Qed.

Lemma sortBy_sorted : forall a (R : a -> a -> bool) `{Transitive _ R} xs,
  (forall x y, ~~ R y x -> R x y) -> StronglySorted R (sortBy R xs).
Proof.
  move=> a R H xs H1.
  elim: xs => [|x xs IHxs] /=.
    by constructor.
  apply: StronglySorted_insert => //.
  exact: (H1 x).
Qed.

Lemma insert_all : forall a (P : a -> bool) (R : a -> a -> bool) x xs,
  all P (insert R x xs) = P x && all P xs.
Proof.
  move=> a P R x.
  elim=> //= [u us IHus].
  rewrite /insert /= -/insert.
  case: (R u x) => //=.
  by rewrite IHus and_swap.
Qed.

Lemma sortBy_all : forall a (P : a -> bool) (R : a -> a -> bool) xs,
  all P xs = all P (sortBy R xs).
Proof.
  move=> a P R.
  elim=> //= [u us IHus].
  by rewrite IHus insert_all.
Qed.

Lemma perm_cons_swap (T : eqType) (x y : T) : forall (xs : seq_predType T),
  perm_eql (x :: y :: xs) (y :: x :: xs).
Proof.
  move=> xs; apply/perm_eqlP.
  rewrite -cat1s perm_catC cat_cons perm_cons perm_catC cat1s.
  exact: perm_eq_refl.
Qed.

Lemma insert_perm (T : eqType) P (x : T) : forall (xs : seq_predType T),
  perm_eql (insert P x xs) (x :: xs).
Proof.
  elim=> //= [y ys IHys]; rewrite /insert.
  case: (P y x) => //=; apply/perm_eqlP.
  rewrite perm_eq_sym perm_cons_swap perm_cons perm_eq_sym -/insert.
  exact/perm_eqlP/IHys.
Qed.

Lemma insert_size : forall a P (x : a) xs,
  size (insert P x xs) = (size xs).+1.
Proof.
  move=> a P x xs.
  elim: xs => //= [y ys IHys].
  rewrite /insert /= -/insert.
  case: (P y x) => //=.
  by rewrite IHys.
Qed.

Lemma proj_rem_uniq (a b : eqType) (f : a -> b) : forall x xs,
  uniq [seq f i | i <- xs] -> uniq [seq f i | i <- rem x xs].
Proof. by move=> x xs; apply/subseq_uniq/map_subseq/rem_subseq. Qed.

Lemma in_proj : forall (a b : eqType) (x : a) (y : b) (xs : seq (a * b)),
  (x \notin [seq fst i | i <- xs]) ||
  (y \notin [seq snd i | i <- xs]) -> (x, y) \notin xs.
Proof.
  move=> a b x y.
  elim=> //= [z zs IHzs] H1.
  move/orP: H1 => [H1|H1];
  rewrite in_cons;
  rewrite in_cons in H1;
  apply/norP;
  move/norP: H1 => [H2 H3];
  (split;
   [ case: z => /= [j k] in H2 *;
     move/eqP in H2;
     apply/eqP;
     move=> Hneg;
     inversion Hneg;
     contradiction
   | apply: IHzs;
     apply/orP ]).
    by left.
  by right.
Qed.

Lemma uniq_proj : forall (a b : eqType) (xs : seq (a * b)),
  uniq [seq fst i | i <- xs] ->
  uniq [seq snd i | i <- xs] -> uniq xs.
Proof.
  move=> a b.
  elim=> //= [x xs IHxs] /andP [H1 H2] /andP [H3 H4].
  case: x => /= [j k] in H1 H3 *.
  apply/andP; split; last exact: IHxs.
  apply: in_proj.
  apply/orP; by left.
Qed.

Lemma subseq_in_cons : forall (a : eqType) x y (xs ys : seq a),
  subseq (x :: xs) (y :: ys) -> x != y -> subseq (x :: xs) ys.
Proof.
  move=> a x y xs ys Hsub Hneq.
  elim: ys => /= [|z zs IHzs] in Hsub *.
    case E: (x == y).
      move/negP: Hneq.
      by rewrite E.
    rewrite E in Hsub.
    inversion Hsub.
  case E: (x == y).
    move/negP: Hneq.
    by rewrite E.
  rewrite E in Hsub.
  assumption.
Qed.

Lemma subseq_sing : forall (a : eqType) (x : a) xs s,
  subseq (x :: xs) s -> subseq [:: x] s.
Proof.
  move=> a x xs s Hsub.
  elim: s => // [y ys IHys] in Hsub *.
  rewrite sub1seq.
  rewrite sub1seq in IHys.
  rewrite in_cons.
  apply/orP.
  case E: (x == y).
    by left.
  right.
  move/negP in E.
  move/negP in E.
  apply: IHys.
  apply: subseq_in_cons.
    exact Hsub.
  exact E.
Qed.

Lemma in_subseq_sing : forall {E : eqType} (s : seq E) v (y : E) ys,
  v = y :: ys -> subseq v s -> y \in s.
Proof.
  move=> E s v y ys ->.
  rewrite -sub1seq.
  exact: subseq_sing.
Qed.

Fixpoint subseq_impl_cons (a : eqType) (x : a) xs s :
  subseq (x :: xs) s -> subseq xs s.
Proof.
  elim: s => //= [z zs IHzs].
  case: xs => // [y ys] in IHzs *.
  case: (x == z).
    case: (y == z).
      exact: subseq_impl_cons.
    exact.
  case: (y == z).
    move=> Hsub.
    specialize (IHzs Hsub).
    apply: subseq_impl_cons.
    exact IHzs.
  exact.
Qed.

Lemma subseq_cons_add : forall (a : eqType) (x : a) xs s,
  subseq xs s -> subseq xs (x :: s).
Proof.
  move=> a x.
  elim=> // [y ys IHys] s Hsub.
  rewrite /=.
  case: (y == x).
    apply: subseq_impl_cons.
    exact Hsub.
  exact.
Qed.

Lemma subseq_cons_rem : forall (a : eqType) (x : a) xs s,
  subseq (x :: xs) s -> subseq xs (rem x s).
Proof.
  move=> a x xs.
  elim=> //= [y ys IHys].
  rewrite eq_sym.
  case E: (y == x); first exact.
  move/IHys => Hsub {IHys}.
  exact: subseq_cons_add.
Qed.

Lemma all_xpredT_true : forall a (xs : seq a), all xpredT xs.
Proof. by move=> ?; elim. Qed.

Fixpoint between_all `(R : rel a) (xs : seq a) : bool :=
  if xs is y :: ys
  then all (R y) ys && between_all R ys
  else true.

Lemma between_all_cat : forall a (xs ys : seq a) (R : rel a),
  between_all R (xs ++ ys) =
  [&& between_all R xs
  ,   between_all R ys
  ,   all (fun x => all (R x) ys) xs
  &   all (fun y => all (R ^~ y) xs) ys
  ].
Proof.
  move=> a xs ys R.
  elim: xs => [|x xs IHxs] in ys *.
    by rewrite /= all_xpredT_true Bool.andb_true_r.
  rewrite cat_cons all_all_cons.
  rewrite /= all_cat {}IHxs /=.
  rewrite !andbA; f_equal.
  rewrite [X in _ = X]andbC.
  rewrite !andbA; f_equal.
  rewrite [X in _ = X]andbC.
  rewrite !andbA; f_equal.
  rewrite Bool.andb_diag.
  by rewrite -!andbA and_swap.
Qed.

Lemma between_all_catC {a} (xs ys : seq a) (R : rel a) (_ : symmetric R) :
  between_all R (xs ++ ys) = between_all R (ys ++ xs).
Proof.
  elim: xs => /= [|x xs IHxs] in ys *.
    by rewrite cats0.
  rewrite IHxs.
  elim: ys => /= [|y ys IHys].
    by rewrite cats0.
  rewrite -IHys !andbA.
  congr (_ && _).
  rewrite !all_cat -!andbA 2!andbA and_swap.
  congr (_ && _).
  rewrite andbC -!andbA [RHS]and_swap.
  congr (_ && _).
  rewrite [RHS]and_swap.
  congr (_ && _).
  by rewrite H.
Qed.

Lemma allpairs_map :
  forall a b c (f : a -> b -> c) (xs : seq a) (ys : seq b),
  [seq f x y | x <- xs, y <- ys] =
  flatten [seq [seq f x y | y <- ys] | x <- xs].
Proof.
  move=> a b c f.
  elim=> //= [x xs IHxs] y.
  congr (_ ++ _).
  exact: IHxs.
Qed.

Instance List_Functor : Functor seq := {
  fmap := fun _ _ => map
}.

Instance List_Applicative : Applicative seq := {
  pure := fun _ x => [:: x];
  ap   := fun _ _ fs xs => [seq f x | f <- fs, x <- xs]
}.

Module ListLaws.

Include MonadLaws.

Program Instance List_FunctorLaws : FunctorLaws seq.
Obligation 1.
  move=> xs.
  by rewrite map_id.
Qed.
Obligation 2.
  move=> xs.
  by rewrite /funcomp /= -!map_comp /funcomp.
Qed.

Program Instance List_ApplicativeLaws : ApplicativeLaws seq.
Obligation 1.
  move=> xs.
  elim: xs => [|x xs IHxs] //=.
  by rewrite IHxs.
Qed.
Obligation 2.
  rewrite cats0.
  elim: u => [|u us IHus] //=.
  rewrite allpairs_cat {}IHus.
  f_equal.
  elim: v => [|v vs IHvs] //=.
  rewrite map_cat {}IHvs.
  elim: w => [|w ws IHws] //=.
  f_equal.
  by rewrite -!map_comp /funcomp.
Qed.
Obligation 4.
  rewrite cats0.
  by elim: u.
Qed.
Obligation 5.
  move=> xs /=.
  by rewrite cats0.
Qed.

End ListLaws.
