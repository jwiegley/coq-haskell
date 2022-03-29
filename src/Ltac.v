Require Import Coq.micromega.Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Ltac inv H  := inversion H; subst; simpl; clear H.
Ltac contra := intros top; contradiction top; clear top.
Ltac invert := intros top; inversion top; clear top.

Tactic Notation "invert" "as" simple_intropattern(pat) :=
  intros top; inversion top as pat; clear top.

Lemma ltn_leq_trans : forall n m p : nat, m < n -> n <= p -> m < p.
Proof. intros. lia. Qed.

Definition comp {a b c} (f : b -> c) (g : a -> b) (x : a) : c := f (g x).
Arguments comp {a b c} f g x /.

Infix "\o" := comp (at level 50).

Theorem comp_id_left : forall {A B} (f : A -> B), id \o f = f.
Proof. reflexivity. Qed.

Hint Resolve comp_id_left.

Theorem comp_id_right : forall {A B} (f : A -> B), f \o id = f.
Proof. reflexivity. Qed.

Hint Resolve comp_id_right.

Theorem comp_assoc : forall {A B C D} (f : C -> D) (g : B -> C) (h : A -> B),
  f \o (g \o h) = (f \o g) \o h.
Proof. reflexivity. Qed.

Hint Resolve comp_assoc.

Theorem uncompose : forall {A B C} (f : B -> C) (g : A -> B) (x : A) (y : C),
  (f \o g) x = f (g x).
Proof. reflexivity. Qed.

Ltac uncompose k :=
  rewrite <- (uncompose k);
  repeat (rewrite <- comp_assoc).

Definition const {A B : Type} (x : A) : B -> A := fun _ => x.

(*
Ltac breakup :=
  repeat match goal with
    | [ H: is_true (_ && _) |- _ ] => move/andP: H => [? ?]
    | [ |- is_true (_ && _) ] => apply/andP; split
    | [ H: is_true (_ || _) |- _ ] => move/orP: H => [?|?]
    | [ |- is_true (_ || _) ] => apply/orP; split
    | [ H: is_true (?X <  ?Y <  ?Z) |- _ ] => move/andP: H => [? ?]
    | [ H: is_true (?X <= ?Y <= ?Z) |- _ ] => move/andP: H => [? ?]
    | [ H: is_true (?X <  ?Y <= ?Z) |- _ ] => move/andP: H => [? ?]
    | [ H: is_true (?X <= ?Y <  ?Z) |- _ ] => move/andP: H => [? ?]
    | [ |- is_true (?X <  ?Y <  ?Z) ] => apply/andP; split
    | [ |- is_true (?X <= ?Y <= ?Z) ] => apply/andP; split
    | [ |- is_true (?X <  ?Y <= ?Z) ] => apply/andP; split
    | [ |- is_true (?X <= ?Y <  ?Z) ] => apply/andP; split
    | [ H: is_true (~~ (?X <  ?Y <  ?Z)) |- _ ] => move/nandP in H
    | [ H: is_true (~~ (?X <= ?Y <  ?Z)) |- _ ] => move/nandP in H
    | [ H: is_true (~~ (?X <  ?Y <= ?Z)) |- _ ] => move/nandP in H
    | [ H: is_true (~~ (?X <= ?Y <= ?Z)) |- _ ] => move/nandP in H
    | [ |- is_true (~~ (?X <  ?Y <  ?Z)) ] => apply/nandP
    | [ |- is_true (~~ (?X <= ?Y <  ?Z)) ] => apply/nandP
    | [ |- is_true (~~ (?X <  ?Y <= ?Z)) ] => apply/nandP
    | [ |- is_true (~~ (?X <= ?Y <= ?Z)) ] => apply/nandP
    end;
  repeat match goal with
    | [ H1: is_true (?X <  ?Y), H2: is_true (?Y <  ?Z) |- _ ] =>
        match goal with
        | [ H: is_true (X < Z) |- _ ] => idtac
        | _ => move: (ltn_trans H1 H2) => ?
        end
    | [ H1: is_true (?X <  ?Y), H2: is_true (?Y <= ?Z) |- _ ] =>
        match goal with
        | [ H: is_true (X < Z) |- _ ] => idtac
        | _ => move: (ltn_leq_trans H1 H2) => ?
        end
    | [ H1: is_true (?X <= ?Y), H2: is_true (?Y <  ?Z) |- _ ] =>
        match goal with
        | [ H: is_true (X < Z) |- _ ] => idtac
        | _ => move: (leq_ltn_trans H1 H2) => ?
        end
    | [ H1: is_true (?X <= ?Y), H2: is_true (?Y <= ?Z) |- _ ] =>
        match goal with
        | [ H: is_true (X <= Z) |- _ ] => idtac
        | _ => move: (leq_trans H1 H2) => ?
        end
    end;
  intuition.

Lemma negneg : forall (a : eqType) (x y : a), ~~ (x != y) -> x = y.
Proof.
  move=> a x y H.
  move/negbTE in H.
  case E: (x == y).
    by move/eqP in E.
  move/eqP in E.
  by move/eqP in H.
Qed.

Lemma negb_eq : forall (T : eqType) (a b : T), ~~ (a != b) = (a == b).
Proof. by move=> T a b; case: (a == b). Qed.

Ltac ordered := abstract (
  intuition;
  breakup;
  repeat match goal with
  | [ H: (_ <= _) = false |- _ ] => move/negbT in H
  | [ H: (_ <  _) = false |- _ ] => move/negbT in H
  end;
  repeat match goal with
  | [ H: is_true (~~ (?X <  ?Y)) |- _ ] => rewrite -leqNgt in H
  | [ H: is_true (~~ (?X <= ?Y)) |- _ ] => rewrite -ltnNge in H
  | [ H: is_true (~~ (?X == ?Y)) |- _ ] => idtac
  | [ H: is_true (~~ (?X != ?Y)) |- _ ] => rewrite negb_eq in H
  | [ |- is_true (~~ (?X <  ?Y)) ] => rewrite -leqNgt
  | [ |- is_true (~~ (?X <= ?Y)) ] => rewrite -ltnNge
  | [ |- is_true (~~ (?X == ?Y)) ] => idtac
  | [ |- is_true (~~ (?X != ?Y)) ] => rewrite negb_eq
  end;
  repeat match goal with
  | [ H: is_true (?X <  ?Y) |- _ ] => move/ltP in H
  | [ H: is_true (?X <= ?Y) |- _ ] => move/leP in H
  | [ H: is_true (?X == ?Y) |- _ ] => move/eqP in H
  | [ H: is_true (?X != ?Y) |- _ ] => move/eqP in H
  | [ |- is_true (?X <  ?Y) ] => apply/ltP
  | [ |- is_true (?X <= ?Y) ] => apply/leP
  | [ |- is_true (?X == ?Y) ] => apply/eqP
  | [ |- is_true (?X != ?Y) ] => apply/eqP
  end;
  omega).

Lemma ltn_addn1 : forall n m, n < m -> n.+1 < m.+1.
Proof. by []. Qed.

Lemma leq_addn1 : forall n m, n <= m -> n.+1 <= m.+1.
Proof. by []. Qed.

Ltac undoubled :=
  breakup;
  do [ apply/ltn_addn1; rewrite ltn_double
     | apply/leq_addn1; rewrite leq_double
     | rewrite doubleS ];
  do [ ordered
     | do [ exact/ltnW/ltnW
          | exact/ltnW
          | exact/leqW/leqW
          | exact/leqW ];
       ordered ].

Lemma Forall_all : forall (T : Type) (a : pred T) (s : seq T),
  reflect (List.Forall a s) (all a s).
Proof.
  move=> T a.
  elim=> [|x xs IHxs] //=.
    by constructor; constructor.
  case E: (a x) => /=.
    case A: (all a xs).
      constructor.
      constructor.
        by rewrite E.
      exact/IHxs.
    constructor.
    move=> Hcontra.
    inversion Hcontra; subst.
    rewrite A in IHxs.
    by move/IHxs in H2.
  constructor.
  move=> Hcontra.
  inversion Hcontra; subst.
  by rewrite E in H1.
Qed.

Ltac match_all :=
  repeat match goal with
  | [ H: List.Forall _ ?Z |- _ ] => move/Forall_all in H
  | [ |- List.Forall _ ?Z ]      => apply/Forall_all
  end;
  abstract match goal with
  | [  H: is_true (all _ ?Z) |- is_true (all _ ?Z) ] =>
      move/allP in H;
      apply/allP;
      intros x_1 H_1;
      specialize (H x_1 H_1);
      clear H_1;
      ordered
  end.
*)

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.
