Require Export Iso.

Generalizable All Variables.

Section Indexed.

Variable A : Type.

Definition inat (P Q : A -> Type) := forall x : A, P x -> Q x.

Notation "s :-> t" := (inat s t) (at level 28).

Definition idx_id {X} : X :-> X.
  unfold ":->". intros. apply X0.
Defined.

Definition idx_compose {X Y Z} : (Y :-> Z) -> (X :-> Y) -> (X :-> Z).
  unfold ":->". intros.
  apply X0. apply X1. apply X2.
Defined.

End Indexed.

Class Category {k} (cat : k -> k -> Type) := {
    id : ∀ {a}, cat a a;
    compose : ∀ {a b c}, cat b c -> cat a b -> cat a c
}.

Program Instance Index_Category {A} : Category (@inat A) := {
    id      := @idx_id A;
    compose := @idx_compose A
}.

Arguments inat [A] _ _.

Notation "s :-> t" := (inat s t) (at level 100).
Notation "f ∘ g" := (compose f g) (at level 40, left associativity).

Class IFunctor {I O} (F : (I -> Type) -> (O -> Type)) := {
    iobj := F;
    imap : forall {X Y}, (X :-> Y) -> (F X :-> F Y);

    ifun_identity : forall {X}, imap (id (a := X)) = id;
    ifun_composition : forall {X Y Z} (f : Y :-> Z) (g : X :-> Y),
      imap f ∘ imap g = imap (f ∘ g)
}.

Arguments imap             [I O F IFunctor X Y] f x _.
Arguments ifun_identity    [I O F IFunctor X].
Arguments ifun_composition [I O F IFunctor X Y Z] f g.

Notation "imap[ M ]  f" := (@imap _ _ M _ _ _ f) (at level 28).
Notation "imap[ M N ]  f" :=
  (@imap _ _ (fun X => M (N X)) _ _ _ f) (at level 26).
Notation "imap[ M N O ]  f" :=
  (@imap _ _ (fun X => M (N (O X))) _ _ _ f) (at level 24).

Coercion iobj : IFunctor >-> Funclass.

Lemma ifun_irrelevance `(F : IFunctor)
  : ∀ (f g : ∀ {X Y}, (X :-> Y) → (F X :-> F Y))
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

Inductive Path {I : Type} : ((I * I) → Type) -> (I * I) → Type :=
  | Stop g : forall {i : I}, Path g (i,i)
  | Link g : forall {i j k : I}, g (i,j) → Path g (j,k) → Path g (i,k).

Arguments Stop [I g i].
Arguments Link [I g i j k] _ _.

Notation "f :-: g" := (Link f g) (at level 50).

Definition path_imap {I} {k h : (I * I) → Type} (f : k :-> h)
  {x : I * I} (p : Path k x) : Path h x.
  induction p as [| ? ? ? ? r rs].
    apply Stop.
  apply (Link (f _ r) (IHrs f)).
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

Inductive IAssign {x : Type} : Type -> x -> x -> Type :=
  | V a k : IAssign a k k.

Infix "::=" := IAssign (at level 50).

Lemma IAssign_unique : forall a (x : a) t (k h : (a ::= x) t), k = h.
Proof.
Admitted.

Definition List a := Path (a ::= (unit,unit)) (unit,unit).

Program Instance KeyIndex_Iso : forall (a : Type) (t : a -> Type) (k : a),
  ((a ::= k) :-> t) ≅ t k.
Obligation 1.
  unfold ":->" in X.
  apply X. constructor.
Defined.
Obligation 2.
  unfold ":->". intros.
  inversion X0; subst.
  apply X.
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
  crush.
Qed.
