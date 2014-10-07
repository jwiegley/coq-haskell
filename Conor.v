Require Export Coq.Program.Equality.
Require Export Iso.
Require Export Tuple.

Generalizable All Variables.

Section Indexed.

Variable A : Type.

Definition inat (P Q : A → Type) := ∀ x : A, P x → Q x.

Notation "s :→ t" := (inat s t) (at level 28).

Definition iid {X} : X :→ X.
  unfold ":→". intros.
  apply X0.
Defined.

Definition icompose {X Y Z} : (Y :→ Z) → (X :→ Y) → (X :→ Z).
  unfold ":→". intros.
  apply X0. apply X1. apply X2.
Defined.

End Indexed.

Arguments inat {A} _ _.
Arguments iid {A X} _ _.
Arguments icompose {A X Y Z} _ _ _ _.

Infix ":→" := inat (at level 100).
Infix ":∘" := icompose (at level 40, left associativity).

Module SimpleCategory.

(** This is a simple treatment of categories, useful here only for proving
    statements from Conor's paper. *)

Class Category {k} (cat : k → k → Type) := {
    id : ∀ {a}, cat a a;
    compose : ∀ {a b c}, cat b c → cat a b → cat a c;

    id_left : ∀ {a} (f : cat a a), compose id f = f;
    id_right : ∀ {a} (f : cat a a), compose f id = f;
    comp_assoc : ∀ {a b c d} (f : cat c d) (g : cat b c) (h : cat a b),
      compose f (compose g h) = compose (compose f g) h
}.

Program Instance Index_Category {A} : Category (@inat A) := {
    id      := @iid A;
    compose := @icompose A
}.

End SimpleCategory.

(** * Indexed functors *)

Class IFunctor {I O} (F : (I → Type) → (O → Type)) := {
    iobj := F;
    imap : ∀ {X Y}, (X :→ Y) → (F X :→ F Y);

    ifun_identity : ∀ {X}, imap (@iid _ X) = iid;
    ifun_composition : ∀ {X Y Z} (f : Y :→ Z) (g : X :→ Y),
      imap f :∘ imap g = imap (f :∘ g)
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

(** * Path *)

(** This is a demonstration of IFunctor, showing "type-aligned lists" as paths
    within a graph. *)

Section Path.

Variable I : Type.
Variable g : (I * I) → Type.

Inductive Path : (I * I) → Type :=
  | Stop : ∀ {i : I}, Path (i,i)
  | Link : ∀ {i j k : I}, g (i,j) → Path (j,k) → Path (i,k).

Notation "f :-: g" := (Link f g) (at level 50).

Fixpoint path_compose {i j k} (x : Path (i,j)) (y : Path (j,k)) : Path (i,k).
Proof.
  intros.
  inversion x; subst. assumption.
  inversion y; subst. assumption.
  apply @Link with (j := j0).
    assumption.
  apply path_compose with (j := j); assumption.
Defined.

Lemma path_right_id : ∀ i j (x : Path (i,j)), path_compose x Stop = x.
Proof. dependent destruction x; reflexivity. Qed.

Hint Rewrite path_right_id.
Hint Resolve path_right_id.

Lemma path_left_id : ∀ i j (x : Path (i,j)), path_compose Stop x = x.
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

Lemma path_compose_spec
  : ∀ {i j k l : I} (x : g (i,j)) (xs : Path (j,k)) (ys : Path (k,l)),
  path_compose (x :-: xs) ys = x :-: path_compose xs ys.
Proof.
  intros.
  dependent destruction xs;
  dependent destruction ys; reflexivity.
Qed.

Import SimpleCategory.

Program Instance Path_Category : Category (fun i j => Path (i,j)) := {
    id      := @Stop;
    compose := fun _ _ _ x y => path_compose y x
}.
Obligation 3.
  dependent destruction f.
    autorewrite with core.
    reflexivity.
  rewrite path_comp_assoc.
  reflexivity.
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

Lemma path_imap_compose : ∀ I (q r : I * I → Type)
  (f : q :→ r) i j k (z : Path q (i,j)) (s : Path q (j,k)),
  path_compose I r (path_imap f z) (path_imap f s) =
  path_imap f (path_compose I q z s).
Proof.
  intros.
  dependent induction z. auto.
  dependent destruction s. auto.
  simpl. f_equal.
  rewrite <- IHz.
  f_equal.
Qed.

(** * IAssign *)

(** IAssign is "a particularly useful constructor of indexed sets, capturing
    that idea of having an element of a given type at a particular key index."
    -- Conor *)

Inductive IAssign {I : Type} (a : Type) (k : I) : I → Type :=
  | V : a → IAssign a k k.

Arguments V {I a k} _.

Infix "::=" := IAssign (at level 50).

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

(** The following shows that a Path whose indices are fixed at unit is
    equivalent to a list. *)

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

(** * IMonad *)

(** We now show that some endo-IFunctors can also be IMonads. *)

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

Definition ijoin {I} `{m : IMonad I} {p} : m (m p) :→ m p :=
  iextend (λ (x : I) (X : m p x), X).

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

Definition iseq `{m : IMonad} {p q r} (f : p :→ m q) (g : q :→ m r)
  : p :→ m r := iextend g :∘ f.

(** Paths are also IMonads. *)

Fixpoint path_join {I : Type} {g : (I * I) → Type} {i}
  (p : Path (Path g) i) : Path g i :=
  match p with
  | Stop k => Stop
  | Link _ _ _ x xs => path_compose I g x (path_join xs)
  end.

Lemma path_join_compose : ∀ I (g : I * I → Type)
  i j k (z : Path (Path g) (i,j)) (s : Path (Path g) (j,k)),
  path_compose I g (path_join z) (path_join s) =
  path_join (path_compose I (Path g) z s).
Proof.
  intros.
  dependent induction z; auto;
  dependent destruction s; simpl; auto.
    rewrite path_right_id.
    reflexivity.
  rewrite <- IHz. simpl.
  repeat rewrite path_comp_assoc.
  reflexivity.
Qed.

Program Instance Path_IMonad {I} : IMonad (@Path I) := {
    iskip := fun p (x : I * I) =>
      (let (i, j) as z return (p z → Path p z) := x in
       λ Y : p (i, j), Y :-: Stop)
}.
Obligation 1.
  unfold ":→" in *. intros.
  apply (imap X) in X0.
  apply path_join in X0.
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
  simpl. rewrite <- IHm.
  rewrite <- path_imap_compose.
  rewrite path_join_compose. reflexivity.
Qed.

(** We now formalize a notion of indexed monads ala Atkey, prove that the
    Atkey definition fulfills them, and thereafter we can trust that Atkey is
    a specialization of IMonad.  We must keep IxAndlicative, however, since we
    do not have applicatives in the general case. *)

Module Atkey.

Class IxFunctor {I O} (F : I → O → Type → Type) :=
{ ixobj := F
; ixmap : ∀ {I O X Y}, (X → Y) → F I O X → F I O Y

; ixfun_identity : ∀ {I O X}, @ixmap I O _ _ (@id X) = id
; ixfun_composition : ∀ {I O X Y Z} (f : Y → Z) (g : X → Y),
    ixmap f ∘ ixmap g = @ixmap I O _ _ (f ∘ g)
}.

Notation "f <$$> g" := (ixmap f g) (at level 28, left associativity).

Notation "ixmap[ M ]  f" := (@ixmap M _ _ _ f) (at level 28).
Notation "ixmap[ M N ]  f" := (@ixmap (fun X => M (N X)) _ _ _ f) (at level 26).
Notation "ixmap[ M N O ]  f" := (@ixmap (fun X => M (N (O X))) _ _ _ f) (at level 24).

Coercion ixobj : IxFunctor >-> Funclass.

Lemma ixfun_irrelevance `(F : IxFunctor)
  : ∀ (f g : ∀ {I O X Y}, (X -> Y) → (F I O X -> F I O Y))
      i i' c c',
  @f = @g →
  {| ixmap := @f
   ; ixfun_identity    := i
   ; ixfun_composition := c |} =
  {| ixmap := @g
   ; ixfun_identity    := i'
   ; ixfun_composition := c' |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.

Section IxFunctor.

Variables I O : Type.
Context `{@IxFunctor I O F}.

Theorem ixfun_identity_x : forall {I O X} (x : F I O X), ixmap id x = id x.
Proof.
  intros.
  rewrite ixfun_identity.
  reflexivity.
Qed.

Theorem ixfun_composition_x
  : forall {I O X Y Z} (f : Y -> Z) (g : X -> Y) (x : F I O X),
  f <$$> (g <$$> x) = (f ∘ g) <$$> x.
Proof.
  intros.
  rewrite <- ixfun_composition.
  reflexivity.
Qed.

End IxFunctor.

Program Instance Atkey_IxFunctor {I : Type} `{H : IFunctor I I F}
  : IxFunctor (Atkey F) := {
    ixmap := fun _ O X Y f x =>
      imap (fun (i : I) (x : (X ::= O) i) =>
              match x with V a => V (f a) end) _ x
}.
Obligation 1.
  destruct H. simpl in *.
  extensionality x.
  unfold id.
  assert ((λ (i : I) (x0 : (X ::= O) i),
      match
        x0 as x1 in ((_ ::= _) i0) return (i0 = i → x1 ~= x0 → (X ::= O) i0)
      with
      | V a => λ (_ : O = i) (_ : V a ~= x0), V a
      end eq_refl JMeq_refl) = iid).
    extensionality i.
    extensionality x0.
    destruct x0. unfold iid. reflexivity.
    rewrite H. clear H.
  rewrite ifun_identity0.
  unfold iid. reflexivity.
Qed.
Obligation 2.
  destruct H. simpl in *.
  unfold compose.
  unfold icompose in *.
  extensionality x.
  remember
    (λ (i : I) (x0 : (Y ::= O) i),
      match
        x0 as x1 in ((_ ::= _) i0) return (i0 = i → x1 ~= x0 → (Z ::= O) i0)
      with
      | V a => λ (_ : O = i) (_ : V a ~= x0), V (f a)
      end eq_refl JMeq_refl) as f'.
  remember
    (λ (i : I) (x0 : (X ::= O) i),
      match
        x0 as x1 in ((_ ::= _) i0)
        return (i0 = i → x1 ~= x0 → (Y ::= O) i0)
      with
      | V a => λ (_ : O = i) (_ : V a ~= x0), V (g a)
      end eq_refl JMeq_refl) as g'.
  specialize (ifun_composition0 (X ::= O) (Y ::= O) (Z ::= O) f' g').
  assert
    ((λ (i : I) (x0 : (X ::= O) i),
       match
         x0 as x1 in ((_ ::= _) i0) return (i0 = i → x1 ~= x0 → (Z ::= O) i0)
       with
       | V a => λ (_ : O = i) (_ : V a ~= x0), V (f (g a))
       end eq_refl JMeq_refl) =
     (λ (x : I) (X2 : (X ::= O) x), f' x (g' x X2))).
    subst.
    extensionality i.
    extensionality x0.
    destruct x0.
    reflexivity.
    rewrite H. clear H.
  rewrite <- ifun_composition0.
  reflexivity.
Qed.

Reserved Notation "f <**> g" (at level 28, left associativity).

Class IxAndlicative {I} (F : I → I → Type → Type) :=
{ is_ixfunctor :> IxFunctor F

; ixpure : ∀ {I X}, X → F I I X
; ixap : ∀ {I J K X Y}, F I J (X → Y) → F J K X → F I K Y
    where "f <**> g" := (ixap f g)

; ixapp_identity : ∀ {I X}, @ixap _ _ I _ _ (@ixpure I _ (@id X)) = id
; ixapp_composition
    : ∀ {I J K L X Y Z}
             (u : F I J (Y → Z)) (v : F J K (X → Y)) (w : F K L X),
    ixpure compose <**> u <**> v <**> w = u <**> (v <**> w)
; ixapp_homomorphism : ∀ {I X Y} (x : X) (f : X → Y),
    ixpure f <**> ixpure x = @ixpure I _ (f x)
; ixapp_interchange : ∀ {I J X Y} (y : X) (u : F I J (X → Y)),
    u <**> ixpure y = ixpure (fun f => f y) <**> u

; app_ixmap_unit : ∀ {I O X Y} (f : X → Y), ixap (ixpure f) = @ixmap _ _ _ _ I O _ _ f
}.

Notation "ixpure/ M" := (@ixpure M _ _) (at level 28).
Notation "ixpure/ M N" := (@ixpure (fun X => M (N X)) _ _) (at level 26).

Notation "ixap[ M ]  f" := (@ixap M _ _ _ f) (at level 28).
Notation "ixap[ M N ]  f" := (@ixap (fun X => M (N X)) _ _ _ f) (at level 26).
Notation "ixap[ M N O ]  f" := (@ixap (fun X => M (N (O X))) _ _ _ f) (at level 24).

Notation "f <**> g" := (ixap f g) (at level 28, left associativity).

Notation "[| f x y .. z |]" := (.. (f <$$> x <**> y) .. <**> z)
    (at level 9, left associativity, f at level 9,
     x at level 9, y at level 9, z at level 9).

Definition ixapp_merge {X Y Z W} (f : X → Y) (g : Z → W)
  (t : X * Z) : Y * W  :=
  match t with (x, z) => (f x, g z) end.

Definition ixapp_prod `{IxAndlicative T F}
  {I J K X Y} (x : F I J X) (y : F J K Y)
  : F I K (X * Y) := pair <$$> x <**> y.

Notation "f *** g" := (ixapp_merge f g) (at level 28, left associativity).

Notation "f ** g" := (ixapp_prod f g) (at level 28, left associativity).

Ltac rewrite_ixapp_homomorphisms :=
  (repeat (rewrite <- app_ixmap_unit);
   rewrite ixapp_homomorphism;
   repeat (rewrite app_ixmap_unit)).

Section IxAndlicative.

Variables I : Type.
Context `{@IxAndlicative I F}.

Theorem app_imap_compose : ∀ I A B (f : A → B),
  ixpure ∘ f = ixmap f ∘ @ixpure _ _ _ I _.
Proof.
  intros.
  extensionality x.
  unfold compose.
  rewrite <- ixapp_homomorphism.
  rewrite app_ixmap_unit.
  reflexivity.
Qed.

Theorem app_imap_compose_x : ∀ J A B (f : A → B) (x : A),
  ixpure (f x) = ixmap f (@ixpure _ F _ J _ x).
Proof.
  intros.
  assert (ixpure (f x) = (@ixpure _ F _ J _ ∘ f) x).
    unfold compose. reflexivity.
  assert (ixmap f (ixpure x) = (ixmap f ∘ @ixpure _ _ _ J _) x).
    unfold compose. reflexivity.
  rewrite H0. rewrite H1.
  rewrite app_imap_compose.
  reflexivity.
Qed.

Theorem ixapp_identity_x : ∀ {I X} {x : F I I X},
  ixap (ixpure (@id X)) x = id x.
Proof.
  intros.
  rewrite app_ixmap_unit.
  apply ixfun_identity_x.
Qed.

Theorem ixapp_homomorphism_2
  : ∀ {I X Y Z} (x : X) (y : Y) (f : X → Y → Z),
  f <$$> ixpure x <**> ixpure y = @ixpure _ _ _ I _ (f x y).
Proof.
  intros.
  rewrite <- ixapp_homomorphism.
  rewrite <- ixapp_homomorphism.
  rewrite app_ixmap_unit.
  reflexivity.
Qed.

(* This theorem was given as an exercise by Brent Yorgey at:

   http://www.haskell.org/haskellwiki/Typeclassopedia#IxAndlicative
*)
Theorem ixapp_flip : ∀ {J K X Y} (x : F J K X) (f : X → Y),
  ixpure f <**> x = ixpure (flip apply) <**> x <**> ixpure f.
Proof.
  intros.
  rewrite ixapp_interchange.
  rewrite <- ixapp_composition.
  rewrite app_ixmap_unit.
  rewrite app_ixmap_unit.
  rewrite ixapp_homomorphism_2.
  unfold compose.
  rewrite app_ixmap_unit.
  reflexivity.
Qed.

Theorem ixapp_embed
  : ∀ {GI G} `{IxAndlicative GI G}
           {I J K X Y} (x : G I J (X → Y)) (y : G J K X),
  ixpure (x <**> y) = ixpure ixap <**> ixpure x <**> @ixpure _ _ _ K _ y.
Proof.
  intros.
  rewrite_ixapp_homomorphisms.
  rewrite <- ixapp_homomorphism.
  rewrite <- app_ixmap_unit.
  reflexivity.
Qed.

Theorem ixapp_split
  : ∀ I J K A B C (f : A → B → C) (x : F I J A) (y : F J K B),
  f <$$> x <**> y = uncurry f <$$> (x ** y).
Proof.
  intros. unfold ixapp_prod.
  repeat (rewrite <- app_ixmap_unit).
  repeat (rewrite <- ixapp_composition; f_equal).
  repeat (rewrite ixapp_homomorphism).
  unfold uncurry, compose. f_equal.
Qed.

Theorem ixapp_naturality
  : ∀ {I J K A B C D}
      (f : A → C) (g : B → D) (u : F I J A) (v : F J K B),
  ixmap (f *** g) (u ** v) = (ixmap f u) ** (ixmap g v).
Proof.
  intros.
  unfold ixapp_prod.
  rewrite <- app_ixmap_unit.
  rewrite ixfun_composition_x.
  repeat (rewrite <- app_ixmap_unit).
  rewrite <- ixapp_composition.
  rewrite <- ixapp_composition.
  rewrite <- ixapp_composition.
  rewrite <- ixapp_composition.
  rewrite ixapp_composition.
  rewrite ixapp_composition.
  f_equal.
  rewrite_ixapp_homomorphisms.
  rewrite ixfun_composition_x.
  rewrite ixfun_composition_x.
  rewrite ixapp_interchange.
  rewrite app_ixmap_unit.
  rewrite ixfun_composition_x.
  f_equal.
Qed.

(*
  Theorem app_left_identity {I A} (v : F I I A) : (F I I unit * v) ≅ v.
  Proof.
    intros.
    unfold app_prod, app_unit.
    rewrite_app_homomorphisms.
    split.
      assert (imap (pair tt) =
              (@from (F (unit * A)) (F A)
                     (Functor_Isomorphism _ LTuple_Isomorphism))).
        reflexivity. rewrite H0. clear H0.
      apply iso_from_x.
      reflexivity.
  Qed.

  Theorem app_right_identity `(v : F A) : (v ** ixpure tt) ≡ v.
  Proof.
    intros.
    unfold app_prod, app_unit.
    rewrite <- app_ixmap_unit.
    rewrite app_interchange.
    rewrite <- app_composition.
    rewrite app_homomorphism.
    rewrite app_homomorphism.
    rewrite app_ixmap_unit.
    unfold compose.
    split.
      assert (imap (fun x : A => (x, tt)) =
              (@from (F (A * unit)) (F A)
                     (Functor_Isomorphism _ RTuple_Isomorphism))).
        reflexivity. rewrite H0.
      apply iso_from_x.
      reflexivity.
  Qed.
*)

Theorem ixapp_embed_left_triple
  : ∀ I J K L A B C
      (u : F I J A) (v : F J K B) (w : F K L C),
  u ** v ** w = left_triple <$$> u <**> v <**> w.
Proof.
  intros.
  unfold ixapp_prod.
  repeat (rewrite <- app_ixmap_unit).
  rewrite <- ixapp_composition.
  f_equal. f_equal.
  rewrite_ixapp_homomorphisms.
  rewrite ixfun_composition_x.
  reflexivity.
Qed.

Theorem ixapp_embed_right_triple
  : ∀ I J K L A B C
      (u : F I J A) (v : F J K B) (w : F K L C),
  u ** (v ** w) = right_triple <$$> u <**> v <**> w.
Proof.
  intros.
  unfold ixapp_prod.
  repeat (rewrite <- app_ixmap_unit).
  rewrite <- ixapp_composition.
  f_equal. f_equal.
  repeat (rewrite app_ixmap_unit).
  rewrite ixfun_composition_x.
  repeat (rewrite <- app_ixmap_unit).
  rewrite <- ixapp_composition.
  f_equal.
  repeat (rewrite app_ixmap_unit).
  rewrite ixfun_composition_x.
  rewrite ixapp_interchange.
  rewrite app_ixmap_unit.
  rewrite ixfun_composition_x.
  unfold compose.
  reflexivity.
Qed.

(*
  Theorem ixapp_associativity
    : ∀ A B C (u : F I J A) (v : F J K B) (w : F K L C),
    ((u ** v) ** w) ≡ (u ** (v ** w)).
  Proof.
    intros.
    rewrite ixapp_embed_left_triple.
    rewrite ixapp_embed_right_triple.
    split; simpl;
    repeat (rewrite <- app_ixmap_unit);
    rewrite <- ixapp_composition;
    rewrite <- ixapp_composition;
    rewrite <- ixapp_composition;
    repeat f_equal;
    repeat (rewrite app_ixmap_unit);
    rewrite ifun_composition_x;
    rewrite ifun_composition_x;
    rewrite <- app_imap_compose_x;
    rewrite ixapp_homomorphism;
    reflexivity.
  Qed.
*)

Definition liftIA2 {I J K A B C} (f : A → B → C)
  (x : F I J A) (y : F J K B) : F I K C :=
  f <$$> x <**> y.

End IxAndlicative.

Program Instance Atkey_IxAndlicative {I : Type} `{H : IMonad I F}
  : IxAndlicative (Atkey F) := {
  ixpure := fun _ _ x => iskip (V x)
}.
Obligation 1.
  pose (@ibind I F H0 H I0 J K (X → Y) Y).
  apply a in X0.
  assumption. intros.
  pose (@ibind I F H0 H J K K X Y).
  apply a0 in X1.
  assumption. intros.
  apply X2 in X3.
  unfold Atkey.
  pose (@ireturn I F H0 H K Y).
  apply a1.
  assumption.
Defined.
Obligation 2.
  unfold Atkey_IxAndlicative_obligation_1.
  extensionality X1. unfold id.
  destruct H. destruct H0. simpl in *.
  rewrite imonad_left_id0.
  destruct is_ifunctor0.
  assert
    ((fun (H0 : I) (x : @IAssign I X I0 H0) =>
         match
           x in (@IAssign _ _ _ y)
           return
             (@iobj I I
                (@iobj I I F
                   (Build_IFunctor I I F imap1 ifun_identity1
                      ifun_composition1))
                (Build_IFunctor I I F imap1 ifun_identity1 ifun_composition1)
                (@IAssign I X I0) y)
         with
         | V a => iskip0 (@IAssign I X I0) I0 (@V I X I0 a)
         end) = @iskip0 _).
    extensionality H1.
    extensionality x.
    destruct x. reflexivity.
    rewrite H. clear H.
  apply (imonad_right_id0 (X ::= I0) (X ::= I0)).
  auto.
Qed.
Obligation 3. Admitted.
Obligation 4. Admitted.
Obligation 5. Admitted.
Obligation 6. Admitted.

Definition ixapp_unit `{IxAndlicative _ F} : F unit unit unit := ixpure tt.

Reserved Notation "m >>= f" (at level 25, left associativity).

Class IxMonad {I} (M : I → I → Type → Type) :=
{ is_ixapplicative :> IxAndlicative M

; ixbind : ∀ {I J K X Y}, M I J X → (X -> M J K Y) → M I K Y
    where "m >>= f" := (ixbind m f)

; ixmonad_left_id : ∀ {I O X Y} (f : X → M I O Y) (x : X),
    ixpure x >>= f = f x
; ixmonad_right_id : ∀ {I O X} (m : M I O X), m >>= ixpure = m
; ixmonad_assoc : ∀ {I J K L X Y Z} (m : M I J X)
    (f : X → M J K Y) (g : Y → M K L Z),
    (m >>= f) >>= g = m >>= (λ x, f x >>= g)
}.

Program Instance Atkey_IxMonad {I : Type} `{H : IMonad I F}
  : IxMonad (Atkey F) := {
  ixbind := @ibind I F _ H
}.
Obligation 1.
  unfold ibind, angbind.
  rewrite imonad_left_id.
  reflexivity.
Qed.
Obligation 2.
  unfold ibind, angbind.
  destruct H0. destruct H. simpl in *.
  assert
    ((fun (H : I) (x : @IAssign I X O H) =>
         match
           x in (@IAssign _ _ _ y)
           return
             (@iobj I I (@iobj I I F is_ifunctor0) is_ifunctor0
                (@IAssign I X O) y)
         with
         | V a => iskip0 (@IAssign I X O) O (@V I X O a)
         end) = @iskip0 _).
    extensionality H.
    extensionality x.
    destruct x.
    reflexivity.
    rewrite H. clear H.
  apply (imonad_right_id0 _ (X ::= O)).
  apply iskip0.
Qed.
Obligation 3.
  unfold ibind, angbind.
  rewrite imonad_assoc.
  f_equal.
  extensionality x.
  extensionality a.
  destruct a.
  reflexivity.
Qed.

End Atkey.

Module Hoare.

Inductive RProd {I} (p q : I → Type) r i :=
  mkRProd : p i → (q :→ r) → RProd p q r i.

Arguments mkRProd {I p q r i} _ _.

Infix ":>>:" := RProd (at level 25, left associativity).
Infix ":&" := mkRProd (at level 25, left associativity).

Program Instance RProd_IFunctor {I} (p q : I → Type) : IFunctor (p :>>: q) := {
    imap := fun _ _ h _ x => match x with p :& k => p :& (h :∘ k) end
}.
Obligation 1.
  extensionality H.
  extensionality x.
  destruct x.
  reflexivity.
Qed.
Obligation 2.
  extensionality H.
  extensionality x.
  destruct x.
  reflexivity.
Qed.

Inductive RSum {I O} (f g : (I → Type) → (O → Type)) (p : I → Type) (i : O) :=
  | InL : f p i → RSum f g p i
  | InR : g p i → RSum f g p i.

Arguments InL {I O f g p i} _.
Arguments InR {I O f g p i} _.

Infix ":+:" := RSum (at level 25, left associativity).

Program Instance RSum_IFunctor {I O} `{IFunctor I O f, IFunctor I O g}
  : IFunctor (f :+: g) := {
    imap := fun _ _ h _ x =>
      match x with
      | InL fp => InL (@imap I O f _ _ _ h _ fp)
      | InR gp => InR (@imap I O g _ _ _ h _ gp)
      end
}.
Obligation 1.
  extensionality H1.
  extensionality x.
  destruct x;
  rewrite ifun_identity; reflexivity.
Qed.
Obligation 2.
  extensionality H1.
  extensionality x.
  destruct x;
  [ destruct H | destruct H0 ];
  simpl in *;
  unfold icompose in *; f_equal;
  specialize (ifun_composition0 X Y Z f0 g0);
  rewrite <- ifun_composition0; reflexivity.
Qed.

Inductive FilePath := FilePath_.

Inductive State := Open | Closed.

Definition FH : (State → Type) → State → Type :=
      ((FilePath ::= Closed) :>>: (fun _ => State))  (* fOpen *)
  :+: ((unit ::= Open) :>>: (option nat ::= Open))   (* fGetC *)
  :+: ((unit ::= Open) :>>: (unit ::= Closed)).      (* fClose *)

Record Signature (I : Type): Type := {
    Operations : I → Type;
    Arities    : forall i : I, Operations i → Type;
    Sorts      : forall (i : I) (op : Operations i), Arities i op → I
}.

Arguments Operations {_} _ i.
Arguments Arities {_} _ {_} op.
Arguments Sorts {_} _ {_} {_} ar.

Definition WFunctor {I} (S : Signature I) (X : I → Type) (i : I) : Type :=
  { op : Operations S i & forall ar : Arities S op, X (Sorts S ar) }.

Inductive Kleene {I} (S : Signature I) (p : I → Type) (i : I) :=
| Ret : p i → Kleene S p i
| Do  : WFunctor S (Kleene S p) i → Kleene S p i.

Arguments Ret {I S p i} _.
Arguments Do {I S p i} _.

Infix ":*" := Kleene (at level 25, left associativity).

(*
Fixpoint Kleene_extend {I} `{IFunctor I I F}
  {p q : I → Type} (f : p :→ Kleene F q) i (x : Kleene F p i)
  {struct x} : Kleene F q i.
Proof.
  destruct x as [y | r ffp].
    apply (f i y).
  apply Do. intros.
  unfold ":→" in *.
  pose (Kleene_extend _ _ _ p q f).
  pose (imap k i).
Admitted.

Program Instance Kleene_IFunctor {I} `{H : IFunctor I I F}
  : IFunctor (Kleene F) := {
    imap := fun X Y f i x =>
      match x with
      | Ret y => Ret (f i y)
      | Do j g => Do j (imap f j g)
      end
}.
Obligation 1.
  extensionality i.
  extensionality x.
  destruct x.
    unfold iid; reflexivity.
  rewrite ifun_identity.
  unfold iid; reflexivity.
Qed.
Obligation 2.
  extensionality i.
  extensionality x.
  destruct x.
    unfold iid; reflexivity.
  rewrite <- ifun_composition.
  unfold icompose. reflexivity.
Qed.

Program Instance Kleene_IMonad {I} `{H : IFunctor I I F}
  : IMonad (Kleene F) := {
    iskip := fun _ _ => Ret;
    iextend := @Kleene_extend I F H
}.
Obligation 2.
  destruct m. reflexivity.
  simpl.
Admitted.
Obligation 3.
Admitted.
*)

End Hoare.

Inductive IState {I} (S P : I → Type) (i : I) :=
  mkIState : (S i → (P i * S i)) → IState S P i.

Arguments mkIState {I S P i} _.

Definition runIState {I} {S P : I → Type} {i} (x : IState S P i) :=
  match x with mkIState f => f end.

Definition iget {I} {S : I → Type} {i} : IState S S i :=
  mkIState (fun s : S i => (s, s)).

Definition igets {I} {S T : I → Type} {i} (f : S :→ T) : IState S T i :=
  mkIState (fun s : S i => (f i s, s)).

Definition iput {I} {S : I → Type} {i} (s : S i) : IState S (const unit) i :=
  mkIState (fun _ : S i => (tt, s)).

Definition imodify {I} (S : I → Type) {i} (f : S :→ S)
  : IState S (const unit) i :=
  mkIState (fun s : S i => (tt, f i s)).

Program Instance IState_IFunctor {I} (S : I → Type)
  : IFunctor (IState S) := {
    imap := fun X Y f i x =>
      mkIState (fun st => let (a,st') := runIState x st in (f i a, st'))
}.
Obligation 1.
  extensionality i.
  extensionality x.
  unfold iid. destruct x.
  f_equal.
  extensionality st. simpl.
  destruct (p st).
  reflexivity.
Qed.
Obligation 2.
  extensionality i.
  extensionality x.
  unfold icompose.
  f_equal.
  extensionality st.
  destruct x.
  simpl.
  destruct (p st).
  reflexivity.
Qed.

Program Instance IState_IMonad {I} (S : I → Type) : IMonad (IState S) := {
    iskip := fun p i x => mkIState (fun st => (x, st));
    iextend := fun p q f i x => mkIState (fun st =>
      let (y, st') := runIState x st in
      runIState (f i y) st')
}.
Obligation 1.
  destruct (f i a). simpl.
  f_equal.
Qed.
Obligation 2.
  destruct m. simpl.
  f_equal.
  extensionality st.
  destruct (p0 st).
  reflexivity.
Qed.
Obligation 3.
  destruct m. simpl.
  f_equal.
  extensionality st.
  destruct (p0 st).
  reflexivity.
Qed.
