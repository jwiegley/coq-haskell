Require Export Coq.Program.Equality.
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

Section Path.

Variable I : Type.
Variable g : (I * I) → Type.

Inductive Path : (I * I) → Type :=
  | Stop : ∀ {i : I}, Path (i,i)
  | Link : ∀ {i j k : I}, g (i,j) → Path (j,k) → Path (i,k).

Fixpoint path_compose {i j k} (x : Path (i,j)) (y : Path (j,k)) : Path (i,k).
Proof.
  intros.
  inversion x; subst. assumption.
  inversion y; subst. assumption.
  apply @Link with (j := j0).
    assumption.
  apply path_compose with (j := j); assumption.
Defined.

Lemma path_right_id : forall i j (x : Path (i,j)), path_compose x Stop = x.
Proof. dependent destruction x; reflexivity. Qed.

Hint Rewrite path_right_id.
Hint Resolve path_right_id.

Lemma path_left_id : forall i j (x : Path (i,j)), path_compose Stop x = x.
Proof. dependent destruction x; reflexivity. Qed.

Hint Rewrite path_left_id.
Hint Resolve path_left_id.

Definition path_comp_assoc
  {i j k l} (x : Path (i,j)) (y : Path (j,k)) (z : Path (k,l)) :
  path_compose x (path_compose y z) = path_compose (path_compose x y) z.
Proof.
  dependent destruction x;
  dependent destruction y;
  dependent destruction z; auto.
  simpl. f_equal.
  dependent induction x; auto.
  simpl. f_equal.
  eapply IHx.
  apply g1.
Qed.

End Path.

Arguments Path {I} g _.
Arguments Stop {I g i}.
Arguments Link {I g i j k} _ _.

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

Definition list_to_Path : ∀ {a}, list a → Path (a ::= (tt, tt)) (tt, tt).
  intros.
  induction X.
    apply Stop.
  apply @Link with (j := tt).
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
  compute.
  extensionality p.
  dependent induction p. auto.
  destruct j.
  rewrite IHp; auto.
  f_equal.
  dependent destruction g.
  reflexivity.
Qed.

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

Definition angbind `{m : IMonad}
  {a j q} (f : a → m q j) : m (a ::= j) :→ m q :=
  iextend ((λ _ x, match x with V a => f a end) : (a ::= j) :→ m q).

Notation "c =>= f" := (angbind f _ c) (at level 25, left associativity).

(** An ordinary monad on indexed types induces an indexed monad on ordinary
    types, packaging the restricted functionality offered by the angelic
    bind. -- Conor *)

Definition Atkey {I : Type} (m : (I → Type) → (I → Type)) i j a :=
  m (a ::= j) i.

Definition ireturn `{m : IMonad} {i a} (x : a) : Atkey m i i a :=
  iskip (V x).

Definition ibind `{m : IMonad} {i j k a b}
  : Atkey m i j a → (a → Atkey m j k b) → Atkey m i k b :=
  fun x f => angbind f _ x.

Infix ">>=" := ibind (at level 25, left associativity).

Definition iseq `{m : IMonad} {p q r} (f : p :→ m q) (g : q :→ m r)
  : p :→ m r := iextend g ∘ f.

Definition ijoin : forall {I : Type} (g : (I * I) → Type) x,
  Path (Path g) x → Path g x.
Proof.
  intros. dependent induction X. apply Stop.
  apply (@path_compose _ _ i j k); assumption.
Defined.

Program Instance Path_IMonad {I} : IMonad (@Path I) := {
    iskip := fun p (x : I * I) =>
      (let (i, j) as z return (p z → Path p z) := x in
       λ Y : p (i, j), Y :-: Stop)
}.
Obligation 1.
  unfold ":→" in *. intros.
  apply (imap X) in X0.
  apply ijoin in X0.
  assumption.
Defined.
Obligation 2.
  unfold Path_IMonad_obligation_1. simpl.
  apply path_right_id.
Qed.
Obligation 3.
  unfold Path_IMonad_obligation_1. simpl.
  dependent induction m. reflexivity.
  specialize (IHm _ f).
  simpl. rewrite IHm.
  dependent destruction m; auto.
Qed.
Obligation 4.
  unfold Path_IMonad_obligation_1. simpl.
  dependent induction m. reflexivity.
  specialize (IHm _ _ f g).
  simpl. rewrite <- IHm.
Admitted.
