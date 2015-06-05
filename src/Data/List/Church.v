(* Church-encoded lists. *)

Require Import Hask.Prelude.
Require Import FunctionalExtensionality.

Generalizable All Variables.

Definition Church (a : Type) := forall r, (a -> r -> r) -> r -> r.

Definition toChurch {a} : seq a -> Church a :=
  fun xs _ c n => foldr c n xs.

Definition fromChurch `(xs : Church a) : seq a := xs _ cons nil.

Axiom Church_parametricity : forall (a : Type)
  (l : forall r : Type, (a -> r -> r) -> r -> r)
  (r : Type) (c : a -> r -> r) (n : r),
  foldr c n (l (seq a) cons [::]) = l r c n.

Definition to_from_Church : forall a (l : Church a),
  toChurch (fromChurch l) = l.
Proof.
  rewrite /Church /toChurch /fromChurch.
  move=> a l.
  extensionality r.
  extensionality c.
  extensionality n.
  exact: Church_parametricity.
Qed.

Definition Church_ind : forall (A : Type) (P : Church A -> Prop),
   P (fun _ c n => n) ->
   (forall (h : A) (t : Church A), P t -> P (fun _ c n => c h (t _ c n))) ->
   forall l : Church A, P l.
Proof.
  rewrite /Church.
  move=> A P Hnil Hcons l.
  rewrite -[l]to_from_Church.
  induction (fromChurch l) as [|x xs IHxs].
    exact: Hnil.
  exact/Hcons/IHxs.
Defined.

Definition Church_length `(xs : Church a) : nat := xs nat (fun _ => plus 1) 0.
Definition Church_append {a} (xs ys : Church a) : Church a :=
  fun _ c n => xs _ c (ys _ c n).

Example Church_append_works :
 fromChurch (Church_append (toChurch [:: 1; 2; 3]) (toChurch [:: 4; 5; 6]))
    = [:: 1; 2; 3; 4; 5; 6].
Proof. reflexivity. Qed.

Theorem Church_length_append : forall a (xs ys : Church a),
  Church_length (Church_append xs ys) = Church_length xs + Church_length ys.
Proof.
  move=> a xs.
  rewrite /Church_length /Church_append. simpl.
  elim/Church_ind: xs => //= [x xs IHxs] ys.
  by rewrite IHxs.
Qed.
