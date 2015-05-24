Require Import Hask.Prelude.
Require Import Hask.Data.List.
Require Import Hask.Data.NonEmpty.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Inductive IntMap (a : Type) := getIntMap of seq (nat * a).

Arguments getIntMap [a] _.

Definition emptyIntMap {a} := @getIntMap a [::].

Definition IntMap_fromList := getIntMap.

Definition IntMap_size : forall a, IntMap a -> nat :=
  fun _ m => let: getIntMap x := m in size x.

(* We needn't bother defining these in Coq, since they only matter to the
   extracted Haskell code, and there we use the definitions from
   [Data.IntMap]. *)
Definition IntMap_lookup : forall a, nat -> IntMap a -> option a :=
  fun _ k m => let: getIntMap x := m in maybeLookup x k.

Definition IntMap_member : forall a, nat -> IntMap a -> bool :=
  fun _ k m => if IntMap_lookup k m is Some _ then true else false.

Definition IntMap_alter : forall a,
  (option a -> option a) -> nat -> IntMap a -> IntMap a :=
  fun _ f k m =>
    let: getIntMap xs := m in @getIntMap _ $
    if IntMap_lookup k m is Some x
    then
      foldr (fun z acc =>
               let: (a, b) := z in
               if a == k
               then if f (Some x) is Some x'
                    then rcons acc (k, x')
                    else acc
               else z :: acc)
            [::] xs
    else if f None is Some x
         then rcons xs (k, x)
         else xs.

Definition IntMap_insert : forall a, nat -> a -> IntMap a -> IntMap a :=
  fun _ k x m => IntMap_alter (fun _ => Some x) k m.

Definition IntMap_map {a b} (f : a -> b) (m : IntMap a) : IntMap b :=
  let: getIntMap xs := m in
  getIntMap (map (fun x => (fst x, f (snd x))) xs).

Definition IntMap_mapWithKey {a b} (f : nat -> a -> b) (m : IntMap a) :
  IntMap b :=
  let: getIntMap xs := m in
  let f k x rest := (fst x, f k (snd x)) :: rest in
  getIntMap (foldr_with_index f [::] xs).

(* The implementation of this function is in LinearScan.Utils.hs *)
Definition IntMap_mergeWithKey' {a b c}
  (combine : nat -> a -> b -> option c)
  (only1 : seq (nat * a) -> seq (nat * c))
  (only2 : seq (nat * b) -> seq (nat * c))
  (m1 : seq (nat * a)) (m2 : seq (nat * b)) : seq (nat * c) := [::].

Definition IntMap_mergeWithKey {a b c} (combine : nat -> a -> b -> option c)
  (only1 : IntMap a -> IntMap c) (only2 : IntMap b -> IntMap c)
  (m1 : IntMap a) (m2 : IntMap b) : IntMap c :=
  let: getIntMap xs1 := m1 in
  let: getIntMap xs2 := m2 in
  let only1' xs :=
    let: getIntMap xs' := only1 (getIntMap xs) in xs' in
  let only2' xs :=
    let: getIntMap xs' := only2 (getIntMap xs) in xs' in
  getIntMap (IntMap_mergeWithKey' combine only1' only2' xs1 xs2).

Definition IntMap_foldl {a b} (f : a -> b -> a) (z : a) (m : IntMap b) : a :=
  let: getIntMap xs := m in foldl (fun acc x => f acc (snd x)) z xs.

Definition IntMap_foldlWithKey
  {a b} (f : a -> nat -> b -> a) (z : a) (m : IntMap b) : a :=
  let: getIntMap xs := m in foldl (fun acc x => f acc (fst x) (snd x)) z xs.

Definition IntMap_toList {a} (m : IntMap a) : seq (nat * a) :=
  let: getIntMap xs := m in xs.

Section EqIntMap.

Variable a : eqType.

Definition eqIntMap (s1 s2 : IntMap a) :=
  match s1, s2 with
  | getIntMap xs, getIntMap ys => xs == ys
  end.

Lemma eqIntMapP : Equality.axiom eqIntMap.
Proof.
  move.
  case=> [s1].
  case=> [s2] /=.
  case: (s1 =P s2) => [<-|neqx]; last by right; case.
  by constructor.
Qed.

Canonical IntMap_eqMixin := EqMixin eqIntMapP.
Canonical IntMap_eqType := Eval hnf in EqType (IntMap a) IntMap_eqMixin.

End EqIntMap.

Definition IntMap_groupOn {a} (p : a -> nat) (l : seq a) :
  IntMap (NonEmpty a) :=
  forFold emptyIntMap l $ fun acc x =>
    let n := p x in
    IntMap_alter (fun mxs => if mxs is Some xs
                             then Some (NE_Cons x xs)
                             else Some [::: x]) n acc.
