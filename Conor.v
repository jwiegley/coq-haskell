Require Export Iso.

Generalizable All Variables.

Section Indexed.

Variable A : Type.

Definition inat (P Q : A → Type) := ∀ x : A, P x → Q x.

Notation "s :→ t" := (inat s t) (at level 28).

Definition idx_id {X} : X :→ X.
  unfold ":→". intros.
  apply X0.
Defined.

Definition idx_compose {X Y Z} : (Y :→ Z) → (X :→ Y) → (X :→ Z).
  unfold ":→". intros.
  apply X0. apply X1. apply X2.
Defined.

End Indexed.

Class Category {k} (cat : k → k → Type) := {
    id : ∀ {a}, cat a a;
    compose : ∀ {a b c}, cat b c → cat a b → cat a c
}.

Program Instance Index_Category {A} : Category (@inat A) := {
    id      := @idx_id A;
    compose := @idx_compose A
}.

Arguments inat [A] _ _.

Notation "s :→ t" := (inat s t) (at level 100).
Notation "f ∘ g" := (compose f g) (at level 40, left associativity).

Class IFunctor {I O} (F : (I → Type) → (O → Type)) := {
    iobj := F;
    imap : ∀ {X Y}, (X :→ Y) → (F X :→ F Y);

    ifun_identity : ∀ {X}, imap (id (a := X)) = id;
    ifun_composition : ∀ {X Y Z} (f : Y :→ Z) (g : X :→ Y),
      imap f ∘ imap g = imap (f ∘ g)
}.

Notation "imap[ M ]  f" := (@imap _ _ M _ _ _ f) (at level 28).
Notation "imap[ M N ]  f" :=
  (@imap _ _ (λ X, M (N X)) _ _ _ f) (at level 26).
Notation "imap[ M N O ]  f" :=
  (@imap _ _ (λ X, M (N (O X))) _ _ _ f) (at level 24).

Coercion iobj : IFunctor >-> Funclass.

Lemma ifun_irrelevance `(F : IFunctor)
  : ∀ (f g : ∀ {X Y}, (X :→ Y) → (F X :→ F Y))
      i i' c c',
  @f = @g →
  {| imap := @f
   ; ifun_identity    := i
   ; ifun_composition := c |} =
  {| imap := @g
   ; ifun_identity    := i'
   ; ifun_composition := c' |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.

Inductive Path {I : Type} (g : (I * I) → Type) : (I * I) → Type :=
  | Stop : ∀ {i : I}, Path g (i,i)
  | Link : ∀ {i j k : I}, g (i,j) → Path g (j,k) → Path g (i,k).

Arguments Stop [I g i].
Arguments Link [I g i j k] _ _.

Notation "f :-: g" := (Link f g) (at level 50).

Definition path_imap {I} {k h : (I * I) → Type} (f : k :→ h)
  {x : I * I} (p : Path k x) : Path h x.
  induction p.
    apply Stop.
  apply (Link (f _ g) IHp).
Defined.

Program Instance Path_IFunctor {I} : @IFunctor (I * I) (I * I) (@Path I) := {
    imap := @path_imap I
}.
Obligation 1.
  compute.
  extensionality x.
  extensionality p. induction p.
    reflexivity.
  f_equal. apply IHp.
Qed.
Obligation 2.
  compute.
  extensionality x.
  extensionality p. induction p.
    reflexivity.
  f_equal. apply IHp.
Qed.

Inductive IAssign {I : Type} (a : Type) (k : I) : I → Type :=
  | V : a → IAssign a k k.

Arguments V {I a k} _.

Infix "::=" := IAssign (at level 50).

Definition Atkey {I : Type} (m : (I → Type) → (I → Type)) i j a :=
  m (a ::= j) i.

Definition list_to_Path : ∀ {a}, list a → Path (a ::= (tt, tt)) (tt, tt).
  intros.
  induction X.
    apply Stop.
  apply Link with (j := tt).
  apply V. apply a0.
  apply IHX.
Defined.

Definition Path_to_list : ∀ {a}, Path (a ::= (tt, tt)) (tt, tt) → list a.
  intros.
  induction X.
    apply nil.
  apply cons.
  inversion g. apply X0.
  apply IHX.
Defined.

Program Instance Path_List_Iso
  : ∀ a, list a ≅ Path (a ::= (tt, tt)) (tt, tt) := {
    to   := list_to_Path;
    from := Path_to_list
}.
Obligation 1.
  extensionality l.
  induction l. reflexivity.
  compute. f_equal.
  apply IHl.
Qed.
Obligation 2.
  extensionality p.
  inversion p.
    auto.
Admitted.                       (* need to do induction on p! *)

Program Instance KeyIndex_Iso : ∀ (a I : Type) (t : I → Type) (k : I),
  ((a ::= k) :→ t) ≅ (a → t k).
Obligation 1.
  unfold ":→" in X.
  apply X. constructor.
  apply X0.
Defined.
Obligation 2.
  unfold ":→". intros.
  inversion X0; subst.
  apply X. apply X1.
Defined.
Obligation 3.
  unfold KeyIndex_Iso_obligation_1.
  unfold KeyIndex_Iso_obligation_2.
  unfold Basics.compose, Datatypes.id.
  extensionality f.
  extensionality x.
  extensionality H.
  inversion H; subst.
  destruct H. simpl.
  unfold eq_rect_r. simpl.
  reflexivity.
Qed.

Reserved Notation "c ?>= f" (at level 25, left associativity).

Class IMonad {I} (m : (I → Type) → (I → Type)) `{IFunctor I I m} := {
    is_ifunctor :> IFunctor m;

    iskip   : ∀ {p}, p :→ m p;
    iextend : ∀ {p q}, (p :→ m q) → (m p :→ m q)
      where "c ?>= f" := (iextend f _ c);

    imonad_left_id : ∀ (p q : I → Type) (f : p :→ m q) (i : I) (a : p i),
      iskip i a ?>= f = f i a;
    imonad_right_id : ∀ (p q : I → Type) (f : p :→ m q) (i : I) (m : m p i),
      m ?>= iskip = m;
    imonad_assoc : ∀ (p q r : I → Type)
      (f : p :→ m q) (g : q :→ m r) (i : I) (m : m p i),
      (m ?>= f) ?>= g = m ?>= (λ x a, f x a ?>= g)
}.

Arguments iskip {I m H IMonad p _} _.
Arguments iextend {I m H IMonad p q _} _ _.

Coercion is_ifunctor : IMonad >-> IFunctor.

Notation "c ?>= f" := (iextend f _ c) (at level 25, left associativity).

Definition ireturn `{m : IMonad} {i a} (x : a) : Atkey m i i a :=
  iskip (V x).

Definition angbind `{m : IMonad}
  {a j q i} (c : m (a ::= j) i) (f : a → m q j) : m q i :=
  c ?>= ((λ _ x, match x with V a => f a end) : forall i, m (a ::= j) i → m q i).

Infix "=>=" := angbind (at level 25, left associativity).

Definition iseq `{m : IMonad} {p q r} (f : p :→ m q) (g : q :→ m r)
  : p :→ m r := iextend g ∘ f.

Program Instance Path_IMonad {I} : IMonad (@Path I).
Obligation 1.
  unfold ":→". intros.
  destruct x.
  apply Link with (j := i0).
    apply X.
  apply Stop.
Defined.
Obligation 2.
  unfold ":→". intros x P.
  destruct x as [i j].
  apply (imap X) in P.
  inversion P; subst.
    apply Stop.
Admitted.
Obligation 3.
Admitted.
Obligation 4.
Admitted.
Obligation 5.
Admitted.

(*************************************************************************)

Inductive IState {I O : Type} (P : relation s) (a : I → Type) : O → Type :=
  | St st : (forall st', P st st' → { st'' : s & a st'' & P st' st'' }) → IState P a st.

Arguments St [s P a] st _.

Definition runIState {s : Type} {P : relation s} {a : s → Type} (st : s) (x : IState P a st)
  : (forall st', P st st' → { st'' : s & a st'' & P st' st'' }) := match x with St _ p => p end.

Definition IState_fmap {s : Type} (P : relation s) {a b : s → Type}
  (f : a :→ b) : IState P a :→ IState P b := λ (st : s) x,
  St st (λ st' H, let p := runIState st x st' H in
                match p with
                | existT2 st'' x H' =>
                  existT2 _ _ st'' (f st'' x) H'
                end).

Program Instance IState_IFunctor {s : Type} (P : relation s) : IFunctor (@IState s P) := {
    imap := @IState_fmap s P
}.
Obligation 1.
  compute.
  extensionality st.
  extensionality x.
  destruct x.
  f_equal.
  extensionality st'.
  extensionality H.
  destruct (s0 st').
  reflexivity.
Qed.
Obligation 2.
  compute.
  extensionality st.
  extensionality x.
  destruct x.
  f_equal.
  extensionality st'.
  extensionality H.
  destruct (s0 st').
  reflexivity.
Qed.

(*
Program Instance IState_IMonad {s : Type} (R : relation s) `{PartialOrder _ R} : IMonad (@IState s R) := {
    iskip := fun P st x =>
      St st (λ st' H, existT2 P (R st') _ x H);

    iextend := fun P Q f st x =>
      St st (λ st' H, let p := runIState st x st' H in
                    match p with
                    | existT2 st'' y H' =>
                      runIState st'' (f st'' y) st' _
                    end)
}.
Obligation 1. intuition. Defined.
Obligation 2. intuition. Defined.
Obligation 4.
Admitted.
Obligation 5.
  compute in *.
  destruct m.
  destruct (s0 st).
    reflexivity.
  f_equal.
  extensionality st'.
  extensionality H'.
  destruct (s0 st').
  f_equal.
Admitted.
Obligation 6.
  compute.
  destruct m.
  destruct (s0 st).
    reflexivity.
  f_equal.
  extensionality st'.
  extensionality H'.
  destruct (s0 st').
    assumption.
  compute.
  destruct (s0 x0).
    crush.
Admitted.

Section IState.

Variable   s : Type.
Hypothesis P : relation s.
Context  `(e : PreOrder s P).

Record StateP (before : s) (a : s → Type) := {
    after  : s;
    result : a after;
    holds  : P before after
}.

Arguments after [before] [a] _.
Arguments result [before] [a] _.
Arguments holds [before] [a] _.

(** The [IState] monad requires that a given equivalence relation hold
    between state transitions. *)
Inductive IState (st : s) (a : s → Type) : Type :=
  | St : StateP st a → IState st a.

Arguments St st [a] _.

Definition runIState (st : s) {a : s → Type} (v : IState st a)
  : StateP st a := match v with St f => f end.

Definition IState_fmap (st : s) {a b : s → Type}
  (f : forall st, a st → b st) (x : IState st a) : IState st b :=
  St st (let sp := runIState st x in
          {| after  := after sp
           ; result := f (after sp) (result sp)
           ; holds  := holds sp
           |}).

Hint Unfold IState_fmap.

Ltac IState_auto :=
  intros; simpl;
  repeat (
    autounfold; unfold id, compose; simpl;
    f_equal; try apply proof_irrelevance; auto;
    match goal with
    | [ |- (fun _ : IState _ => _) = (fun _ : IState _ => _) ] =>
        extensionality sx
    | [ |- (fun _ : s => _) = _ ] =>
        extensionality st
    | [ st : s, sp : forall st : s, StateP st _ |- _ ] =>
        destruct (sp st)
    | [ sx : IState _ |- _ ] => destruct sx as [sp]
    | [ |- St _ = St _ ] => f_equal
    end).

Obligation Tactic := IState_auto.

End IState.

Program Instance IState_IFunctor : IFunctor IState := {
    fmap := IState_fmap
}.
*)