Require Export Coq.Program.Equality.
Require Export Iso.
Require Export Tuple.

Generalizable All Variables.

Section Indexed.

Variable A : Type.

Definition transp (P Q : A → Type) := ∀ x : A, P x → Q x.

Notation "s :→ t" := (transp s t) (at level 28).

Definition pid {X} : X :→ X.
  unfold ":→". intros.
  apply X0.
Defined.

Definition pcompose {X Y Z} : (Y :→ Z) → (X :→ Y) → (X :→ Z).
  unfold ":→". intros.
  apply X0. apply X1. apply X2.
Defined.

End Indexed.

Arguments transp {A} _ _.
Arguments pid {A X} _ _.
Arguments pcompose {A X Y Z} _ _ _ _.

Infix ":→" := transp (at level 100).
Infix ":∘" := pcompose (at level 40, left associativity).

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

Program Instance Index_Category {A} : Category (@transp A) := {
    id      := @pid A;
    compose := @pcompose A
}.

End SimpleCategory.

(** * Predicate functors *)

Class PFunctor {I O} (F : (I → Type) → (O → Type)) := {
    pobj := F;
    pmap : ∀ {X Y}, (X :→ Y) → (F X :→ F Y);

    pfun_identity : ∀ {X}, pmap (@pid _ X) = pid;
    pfun_composition : ∀ {X Y Z} (f : Y :→ Z) (g : X :→ Y),
      pmap f :∘ pmap g = pmap (f :∘ g)
}.

Notation "pmap[ M ]  f" := (@pmap _ _ M _ _ _ f) (at level 28).
Notation "pmap[ M N ]  f" :=
  (@pmap _ _ (λ X, M (N X)) _ _ _ f) (at level 26).
Notation "pmap[ M N O ]  f" :=
  (@pmap _ _ (λ X, M (N (O X))) _ _ _ f) (at level 24).

Coercion pobj : PFunctor >-> Funclass.

Lemma pfun_irrelevance `(F : PFunctor)
  : ∀ (f g : ∀ {X Y}, (X :→ Y) → (F X :→ F Y))
      i i' c c',
  @f = @g →
  {| pmap := @f
   ; pfun_identity    := i
   ; pfun_composition := c |} =
  {| pmap := @g
   ; pfun_identity    := i'
   ; pfun_composition := c' |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.

(** * Path *)

(** This is a demonstration of PFunctor, showing "type-aligned lists" as paths
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

Lemma path_compose_spec
  : ∀ {i j k l : I} (x : g (i,j)) (xs : Path (j,k)) (ys : Path (k,l)),
  path_compose (x :-: xs) ys = x :-: path_compose xs ys.
Proof.
  intros.
  dependent destruction xs;
  dependent destruction ys; reflexivity.
Qed.

Definition path_comp_assoc
  {i j k l} (x : Path (i,j)) (y : Path (j,k)) (z : Path (k,l)) :
  path_compose x (path_compose y z) = path_compose (path_compose x y) z.
Proof.
  dependent destruction x;
  dependent destruction y;
  dependent destruction z; auto.
  dependent induction x.
    reflexivity.
  rewrite path_compose_spec.
  rewrite IHx.
  rewrite <- path_compose_spec.
  rewrite <- path_compose_spec.
  reflexivity.
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

Definition path_pmap {I} {k h : (I * I) → Type} (f : k :→ h)
  {x : I * I} (p : Path k x) : Path h x.
  induction p.
    apply Stop.
  apply (Link (f _ g) IHp).
Defined.

Program Instance Path_PFunctor {I} : @PFunctor (I * I) (I * I) (@Path I) := {
    pmap := @path_pmap I
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

Lemma path_pmap_compose : ∀ I (q r : I * I → Type)
  (f : q :→ r) i j k (z : Path q (i,j)) (s : Path q (j,k)),
  path_compose I r (path_pmap f z) (path_pmap f s) =
  path_pmap f (path_compose I q z s).
Proof.
  intros.
  dependent induction z. auto.
  dependent destruction s. auto.
Admitted.

(** * PAssign *)

(** PAssign is "a particularly useful constructor of indexed sets, capturing
    that idea of having an element of a given type at a particular key index."
    -- Conor *)

Inductive PAssign {I : Type} (a : Type) (k : I) : I → Type :=
  | V : a → PAssign a k k.

Arguments V {I a k} _.

Infix "::=" := PAssign (at level 50).

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

(** * PMonad *)

(** We now show that some endo-PFunctors can also be PMonads. *)

Reserved Notation "c ?>= f" (at level 25, left associativity).

Class PMonad {I} (m : (I → Type) → (I → Type)) `{PFunctor I I m} := {
    is_pfunctor :> PFunctor m;

    pskip   : ∀ {p}, p :→ m p;
    pextend : ∀ {p q}, (p :→ m q) → (m p :→ m q)
      where "c ?>= f" := (pextend f _ c);

    imonad_left_id : ∀ (p q : I → Type) (f : p :→ m q) (i : I) (a : p i),
      pskip i a ?>= f = f i a;
    imonad_right_id : ∀ (p q : I → Type) (f : p :→ m q) (i : I) (m : m p i),
      m ?>= pskip = m;
    imonad_assoc : ∀ (p q r : I → Type)
      (f : p :→ m q) (g : q :→ m r) (i : I) (m : m p i),
      (m ?>= f) ?>= g = m ?>= (λ x a, f x a ?>= g)
}.

Arguments pskip {I m H PMonad p _} _.
Arguments pextend {I m H PMonad p q _} _ _.

Coercion is_pfunctor : PMonad >-> PFunctor.

Notation "c ?>= f" := (pextend f _ c) (at level 25, left associativity).

Definition angbind `{m : PMonad}
  {a j q} (f : a → m q j) : m (a ::= j) :→ m q :=
  pextend ((λ _ x, match x with V a => f a end) : (a ::= j) :→ m q).

Notation "c =>= f" := (angbind f _ c) (at level 25, left associativity).

Definition pjoin {I} `{m : PMonad I} {p} : m (m p) :→ m p :=
  pextend (λ (x : I) (X : m p x), X).

(** An ordinary monad on indexed types induces an indexed monad on ordinary
    types, packaging the restricted functionality offered by the angelic
    bind. -- Conor *)

Definition Atkey {I : Type} (m : (I → Type) → (I → Type)) i j a :=
  m (a ::= j) i.

Definition ireturn `{m : PMonad} {i a} (x : a) : Atkey m i i a :=
  pskip (V x).

Definition ibind `{m : PMonad} {i j k a b}
  : Atkey m i j a → (a → Atkey m j k b) → Atkey m i k b :=
  fun x f => angbind f _ x.

Definition iseq `{m : PMonad} {p q r} (f : p :→ m q) (g : q :→ m r)
  : p :→ m r := pextend g :∘ f.

(** Paths are also PMonads. *)

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

Program Instance Path_PMonad {I} : PMonad (@Path I) := {
    pskip := fun p (x : I * I) =>
      (let (i, j) as z return (p z → Path p z) := x in
       λ Y : p (i, j), Y :-: Stop)
}.
Obligation 1.
  unfold ":→" in *. intros.
  apply (pmap X) in X0.
  apply path_join in X0.
  assumption.
Defined.
Obligation 2.
  unfold Path_PMonad_obligation_1. simpl.
  apply path_right_id.
Qed.
Obligation 3.
  unfold Path_PMonad_obligation_1. simpl.
  dependent induction m. reflexivity.
  specialize (IHm _ f).
  simpl. rewrite IHm.
  dependent destruction m; auto.
Qed.
Obligation 4.
  unfold Path_PMonad_obligation_1. simpl.
  dependent induction m. reflexivity.
  simpl. rewrite <- IHm.
  rewrite <- path_pmap_compose.
  rewrite path_join_compose. reflexivity.
Qed.

(** We now formalize a notion of indexed monads ala Atkey, prove that the
    Atkey definition fulfills them, and thereafter we can trust that Atkey is
    a specialization of PMonad.  We must keep IxApplicative, however, since we
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

Program Instance Atkey_IxFunctor {I : Type} `{H : PFunctor I I F}
  : IxFunctor (Atkey F) := {
    ixmap := fun _ O X Y f x =>
      pmap (fun (i : I) (x : (X ::= O) i) =>
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
      end eq_refl JMeq_refl) = pid).
    extensionality i.
    extensionality x0.
    destruct x0. unfold pid. reflexivity.
    rewrite H. clear H.
  rewrite pfun_identity0.
  unfold pid. reflexivity.
Qed.
Obligation 2.
  destruct H. simpl in *.
  unfold compose.
  unfold pcompose in *.
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
  specialize (pfun_composition0 (X ::= O) (Y ::= O) (Z ::= O) f' g').
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
  rewrite <- pfun_composition0.
  reflexivity.
Qed.

Reserved Notation "f <**> g" (at level 28, left associativity).

Class IxApplicative {I} (F : I → I → Type → Type) :=
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

Definition ixapp_prod `{IxApplicative T F}
  {I J K X Y} (x : F I J X) (y : F J K Y)
  : F I K (X * Y) := pair <$$> x <**> y.

Notation "f *** g" := (ixapp_merge f g) (at level 28, left associativity).

Notation "f ** g" := (ixapp_prod f g) (at level 28, left associativity).

Ltac rewrite_ixapp_homomorphisms :=
  (repeat (rewrite <- app_ixmap_unit);
   rewrite ixapp_homomorphism;
   repeat (rewrite app_ixmap_unit)).

Section IxApplicative.

Variables I : Type.
Context `{@IxApplicative I F}.

Theorem app_pmap_compose : ∀ I A B (f : A → B),
  ixpure ∘ f = ixmap f ∘ @ixpure _ _ _ I _.
Proof.
  intros.
  extensionality x.
  unfold compose.
  rewrite <- ixapp_homomorphism.
  rewrite app_ixmap_unit.
  reflexivity.
Qed.

Theorem app_pmap_compose_x : ∀ J A B (f : A → B) (x : A),
  ixpure (f x) = ixmap f (@ixpure _ F _ J _ x).
Proof.
  intros.
  assert (ixpure (f x) = (@ixpure _ F _ J _ ∘ f) x).
    unfold compose. reflexivity.
  assert (ixmap f (ixpure x) = (ixmap f ∘ @ixpure _ _ _ J _) x).
    unfold compose. reflexivity.
  rewrite H0. rewrite H1.
  rewrite app_pmap_compose.
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

   http://www.haskell.org/haskellwiki/Typeclassopedia#IxApplicative
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
  : ∀ {GI G} `{IxApplicative GI G}
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
  repeat (rewrite <- ixapp_composition).
  repeat (rewrite ixapp_homomorphism).
  unfold uncurry, compose.
  reflexivity.
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
  rewrite_ixapp_homomorphisms.
  rewrite ixfun_composition_x.
  rewrite ixfun_composition_x.
  rewrite ixapp_interchange.
  rewrite app_ixmap_unit.
  rewrite ixfun_composition_x.
  reflexivity.
Qed.

(*
  Theorem app_left_identity {I A} (v : F I I A) : (F I I unit * v) ≅ v.
  Proof.
    intros.
    unfold app_prod, app_unit.
    rewrite_app_homomorphisms.
    split.
      assert (pmap (pair tt) =
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
      assert (pmap (fun x : A => (x, tt)) =
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
  repeat (rewrite app_ixmap_unit).
  rewrite ixfun_composition_x.
  repeat (rewrite <- app_ixmap_unit).
  rewrite <- ixapp_composition.
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
    rewrite pfun_composition_x;
    rewrite pfun_composition_x;
    rewrite <- app_pmap_compose_x;
    rewrite ixapp_homomorphism;
    reflexivity.
  Qed.
*)

Definition liftIA2 {I J K A B C} (f : A → B → C)
  (x : F I J A) (y : F J K B) : F I K C :=
  f <$$> x <**> y.

End IxApplicative.

Program Instance Atkey_IxApplicative {I : Type} `{H : PMonad I F}
  : IxApplicative (Atkey F) := {
  ixpure := fun _ _ x => pskip (V x)
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
  unfold Atkey_IxApplicative_obligation_1.
  extensionality X1. unfold id.
  destruct H. destruct H0. simpl in *.
  rewrite imonad_left_id0.
  destruct is_pfunctor0.
  assert
    ((fun (H0 : I) (x : @PAssign I X I0 H0) =>
         match
           x in (@PAssign _ _ _ y)
           return
             (@pobj I I
                (@pobj I I F
                   (Build_PFunctor I I F pmap1 pfun_identity1
                      pfun_composition1))
                (Build_PFunctor I I F pmap1 pfun_identity1 pfun_composition1)
                (@PAssign I X I0) y)
         with
         | V a => pskip0 (@PAssign I X I0) I0 (@V I X I0 a)
         end) = @pskip0 _).
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

Definition ixapp_unit `{IxApplicative _ F} : F unit unit unit := ixpure tt.

Reserved Notation "m >>= f" (at level 25, left associativity).

Class IxMonad {I} (M : I → I → Type → Type) :=
{ is_ixapplicative :> IxApplicative M

; ixbind : ∀ {I J K X Y}, M I J X → (X -> M J K Y) → M I K Y
    where "m >>= f" := (ixbind m f)

; ixmonad_left_id : ∀ {I O X Y} (f : X → M I O Y) (x : X),
    ixpure x >>= f = f x
; ixmonad_right_id : ∀ {I O X} (m : M I O X), m >>= ixpure = m
; ixmonad_assoc : ∀ {I J K L X Y Z} (m : M I J X)
    (f : X → M J K Y) (g : Y → M K L Z),
    (m >>= f) >>= g = m >>= (λ x, f x >>= g)
}.

Program Instance Atkey_IxMonad {I : Type} `{H : PMonad I F}
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
    ((fun (H : I) (x : @PAssign I X O H) =>
         match
           x in (@PAssign _ _ _ y)
           return
             (@pobj I I (@pobj I I F is_pfunctor0) is_pfunctor0
                (@PAssign I X O) y)
         with
         | V a => pskip0 (@PAssign I X O) O (@V I X O a)
         end) = @pskip0 _).
    extensionality H.
    extensionality x.
    destruct x.
    reflexivity.
    rewrite H. clear H.
  apply (imonad_right_id0 _ (X ::= O)).
  apply pskip0.
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

Module Kleene.

Record Signature (I O : Type) : Type := {
    Operations : O → Type;
    Arities    : forall o : O, Operations o → Type;
    Sorts      : forall (o : O) (op : Operations o), Arities o op → I
}.

Arguments Operations {I O} _ i.
Arguments Arities {I O} _ {_} op.
Arguments Sorts {I O} _ {_} {_} ar.

Infix "▷" := Signature (at level 60) : type_scope.
Infix "o ◁ a / s" := ({| Operations := o
                       ; Arities := a
                       ; Sorts := s |}) (at level 40).

Record WFunctor {I O} (S : I ▷ O) (X : I → Type) (o : O) : Type := {
    op : Operations S o;
    ar : Arities S op;
    xx : X (Sorts S ar)
}.

Arguments op {I O S X} o _.
Arguments ar {I O S X} o _.
Arguments xx {I O S X} o _.

Coercion op : WFunctor >-> Operations.
Coercion WFunctor : Signature >-> Funclass.

Program Instance WFunctor_PFunctor {I O} (S : I ▷ O) : PFunctor (WFunctor S).
Obligation 1.
  unfold ":→". intros.
  destruct X1.
  eexists.
  apply X0 in xx0. apply xx0.
Defined.
Obligation 2.
  compute.
  extensionality x.
  extensionality F.
  destruct F. reflexivity.
Qed.
Obligation 3.
  compute.
  extensionality x.
  extensionality F.
  destruct F. reflexivity.
Qed.

Inductive Kleene {I O} (S : I ▷ O) (p : I → Type) (i : I) :=
| Ret : p i → Kleene S p i
| Do  : forall o : O, WFunctor S (Kleene S p) o → Kleene S p i.

Arguments Ret {I O S p i} _.
Arguments Do {I O S p i} o _.

Infix ":*" := Kleene (at level 25, left associativity).

Fixpoint Kleene_extend {I O} (F : I ▷ O)
  {p q : I → Type} (f : p :→ Kleene F q) i (x : Kleene F p i)
  {struct x} : Kleene F q i.
Proof.
  destruct x as [y | r].
    apply (f i y).
  apply (Do r).
  destruct w.
  eexists.
  apply (Kleene_extend _ _ _ p q f).
  apply xx0.
Defined.

Fixpoint Kleene_map {I O} (F : I ▷ O)
  {X Y} (f : X :→ Y) i (x : (F :* X) i) {struct x} : (F :* Y) i.
Proof.
  destruct x.
    apply (Ret (f i x)).
  apply (Do o).
  destruct w.
  eexists.
  apply (Kleene_map I O F X Y f).
  apply xx0.
Defined.

Fixpoint Kleene_identity {I O} (F : I ▷ O)
  {X : I → Type} {i : I} (x : (F :* X) i) :
  Kleene_map F pid i x = pid i x.
Proof.
  destruct x. reflexivity.
  destruct w.
  unfold pid in *. simpl.
  f_equal. f_equal.
  apply Kleene_identity.
Qed.

Fixpoint Kleene_composition {I O} (F : I ▷ O)
  (X Y Z : I → Type) (f : Y :→ Z) (g : X :→ Y)
  (i : I) (x : (F :* X) i) {struct x} :
  (Kleene_map F f :∘ Kleene_map F g) i x = Kleene_map F (f :∘ g) i x.
Proof.
  unfold pcompose.
  destruct x. reflexivity.
  destruct w. simpl.
  f_equal. f_equal.
  apply Kleene_composition.
Qed.

Program Instance Kleene_PFunctor {I O} (F : I ▷ O)
  : PFunctor (Kleene F) := {
    pmap := fun _ _ => Kleene_map F
}.
Obligation 1.
  extensionality i.
  extensionality x.
  apply Kleene_identity.
Qed.
Obligation 2.
  extensionality i.
  extensionality x.
  apply Kleene_composition.
Qed.

Fixpoint Kleene_left_id {I O} (F : I ▷ O)
  (p q : I → Type) (f : p :→ F :* q) (i : I) (m : (F :* p) i) :
  Kleene_extend F (λ H : I, Ret) i m = m.
Proof.
  destruct m. reflexivity.
  destruct w. simpl.
  f_equal. f_equal.
  apply (Kleene_left_id I O F p q).
  assumption.
Qed.

Fixpoint Kleene_assoc {I O} (F : I ▷ O)
  (p q r : I → Type) (f : p :→ F :* q) (g : q :→ F :* r)
  (i : I) (m : (F :* p) i) :
  Kleene_extend F g i (Kleene_extend F f i m) =
  Kleene_extend F (λ (x : I) (a : p x), Kleene_extend F g x (f x a)) i m.
Proof.
  destruct m. reflexivity.
  destruct w. simpl.
  f_equal. f_equal.
  apply (Kleene_assoc I O F p q r).
Qed.

Program Instance Kleene_PMonad {I O} (F : I ▷ O)
  : PMonad (Kleene F) := {
    pskip := fun _ _ => Ret;
    pextend := @Kleene_extend I O F
}.
Obligation 2.
  apply (Kleene_left_id F p q).
  assumption.
Qed.
Obligation 3.
  apply (Kleene_assoc F p q r).
Qed.

End Kleene.

Module IAlgebra.

Inductive RProd {I} (p q r : I → Type) (i : I) :=
  mkRProd : p i → (q :→ r) → RProd p q r i.

Arguments mkRProd {I p q r i} _ _.

Infix ":>>:" := RProd (at level 25, left associativity).
Infix ":&" := mkRProd (at level 25, left associativity).

Program Instance RProd_PFunctor {I} (p q : I → Type) : PFunctor (p :>>: q) := {
    pmap := fun _ _ h _ x => match x with p :& k => p :& (h :∘ k) end
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

Program Instance RSum_PFunctor {I O} `{PFunctor I O f, PFunctor I O g}
  : PFunctor (f :+: g) := {
    pmap := fun _ _ h _ x =>
      match x with
      | InL fp => InL (@pmap I O f _ _ _ h _ fp)
      | InR gp => InR (@pmap I O g _ _ _ h _ gp)
      end
}.
Obligation 1.
  extensionality H1.
  extensionality x.
  destruct x;
  rewrite pfun_identity; reflexivity.
Qed.
Obligation 2.
  extensionality H1.
  extensionality x.
  destruct x;
  [ destruct H | destruct H0 ];
  simpl in *;
  unfold pcompose in *; f_equal;
  specialize (pfun_composition0 X Y Z f0 g0);
  rewrite <- pfun_composition0; reflexivity.
Qed.

End IAlgebra.

Module SAlgebra.

Import Kleene.

Definition 𝒫 (X : Type) := X → Type.

Definition Alg {O} (Σ : O ▷ O) (X : 𝒫 O) : Type := Σ X :→ X.

(* jww (2014-10-10): WRONG *)
Definition sdo {O C X} : @Alg O C (C :* X).
Proof.
  unfold Alg, ":→". intros.
  apply (Do x).
  apply X0.
Defined.

(* jww (2014-10-10): WRONG *)
Definition generic {O} {Σ : O ▷ O} `{PMonad _ Σ} {o : O} (p : Operations Σ o)
  : (Σ :* (λ o', forall a : Arities Σ p, Sorts Σ a = o')) o.
Proof.
  apply pskip. intros.
Admitted.

(*
Inductive μ {O} (Σ : O ▷ O) (o : O) : Type := sup : Alg Σ (μ Σ) → μ Σ o.

Fixpoint iter {O} {C : O ▷ O} {X} (φ : Alg C X)
  {o : O} (x : μ C o) {struct x} : X o :=
  match x with
  | sup p k => φ p (pmap (fun a y => @iter O C X φ a y) p k)
  end.
*)

Definition sid {O} : O ▷ O :=
  {| Operations := λ _, True
   ; Arities    := λ _ _, True
   ; Sorts      := λ o _ _, o |}.

(*
Definition sconst {I O} (p : 𝒫 O) : I ▷ O :=
  {| Operations := p
   ; Arities    := λ _ _, False
   ; Sorts      := λ x _ unit, undefined |}.
*)

Definition sor {I O} (x y : I ▷ O) : I ▷ O :=
  match x with {| Operations := P₁
                ; Arities    := A₁
                ; Sorts      := s₁ |} =>
  match y with {| Operations := P₂
                ; Arities    := A₂
                ; Sorts      := s₂ |} =>
  {| Operations := λ x, P₁ x + P₂ x

   ; Arities := λ o op,
       match op with
       | inl op' => A₁ o op'
       | inr op' => A₂ o op'
       end

   ; Sorts := λ o op,
       match op with
       | inl op' => s₁ o op'
       | inr op' => s₂ o op'
       end
   |}
  end
  end.

(* This one is written using tactics because the dependent matching required
   is rather ugly. *)
Definition sand {I O} (x y : I ▷ O) : I ▷ O.
  destruct x. destruct y.
  eapply
    {| Operations := λ x, Operations0 x * Operations1 x
     ; Arities    := λ o op, let (op₁, op₂) := op in
                             Arities0 o op₁ + Arities1 o op₂ |}.
  Grab Existential Variables.
  intros.
  destruct op0.
  destruct X.
    apply (Sorts0 o o0 a).
  apply (Sorts1 o o1 a).
Defined.

Definition State (S : Set) : S ▷ S :=
  sor {| Operations := λ _, True
       ; Arities    := λ s _, forall s' : S, s = s'
       ; Sorts      := λ s _ _, s
       |}
      {| Operations := λ _, S
       ; Arities    := λ _ _, True
       ; Sorts      := λ _ s _, s
       |}.

(*
Definition get {S} {s : S} : (State S :* ((forall s' : S, s = s') ::= s)) s.

Definition put {S} {s s' : S} : (State S :* (unit ::= s')) s.
*)

End SAlgebra.

Module Hoare.

Import Kleene.

Inductive FilePath := FilePath_.

Inductive State := Open | Closed.

(*
Definition FH' : (State → Type) → State → Type :=
      ((FilePath ::= Closed) :>>: (fun _ => State))  (* fOpen *)
  :+: ((unit ::= Open) :>>: (option nat ::= Open))   (* fGetC *)
  :+: ((unit ::= Open) :>>: (unit ::= Closed)).      (* fClose *)

Definition FH : Signature State :=
  {| Operations := fun st : State => State -> Type
   ; Arities    := fun (st : State) ops => FH' ops st
   ; Sorts      := fun (st : State) ops ars => st |}.
*)

(*
Definition fOpen (p : FilePath) : (FH :* (const State)) Closed.
Proof.
  apply Do.
  apply {| op := _
         ; ar := _
         ; xx := @Ret _ _ _
         |}.
  eexists.
  apply Ret.
  apply Closed.
  Grab Existential Variables.
  constructor.
  constructor.
Defined.

Definition fGetC : (FH :* (Maybe Char := Open)) Open :=
  Do (InR (InL (V () :& k))).

Definition fClose : (FH :* (unit := Closed)) Open :=
  Do (InR (InR (V () :& k))).
*)

End Hoare.

Module PState.

Inductive PState {I} (S P : I → Type) (i : I) :=
  mkPState : (S i → (P i * S i)) → PState S P i.

Arguments mkPState {I S P i} _.

Definition runPState {I} {S P : I → Type} {i} (x : PState S P i) :=
  match x with mkPState f => f end.

Definition pget {I} {S : I → Type} {i} : PState S S i :=
  mkPState (fun s : S i => (s, s)).

Definition pgets {I} {S T : I → Type} {i} (f : S :→ T) : PState S T i :=
  mkPState (fun s : S i => (f i s, s)).

Definition pput {I} {S : I → Type} {i} (s : S i) : PState S (const unit) i :=
  mkPState (fun _ : S i => (tt, s)).

Definition pmodify {I} (S : I → Type) {i} (f : S :→ S)
  : PState S (const unit) i :=
  mkPState (fun s : S i => (tt, f i s)).

Program Instance PState_PFunctor {I} (S : I → Type)
  : PFunctor (PState S) := {
    pmap := fun X Y f i x =>
      mkPState (fun st => let (a,st') := runPState x st in (f i a, st'))
}.
Obligation 1.
  extensionality i.
  extensionality x.
  unfold pid. destruct x.
  f_equal.
  extensionality st. simpl.
  destruct (p st).
  reflexivity.
Qed.
Obligation 2.
  extensionality i.
  extensionality x.
  unfold pcompose.
  f_equal.
  extensionality st.
  destruct x.
  simpl.
  destruct (p st).
  reflexivity.
Qed.

Program Instance PState_PMonad {I} (S : I → Type) : PMonad (PState S) := {
    pskip := fun p i x => mkPState (fun st => (x, st));
    pextend := fun p q f i x => mkPState (fun st =>
      let (y, st') := runPState x st in
      runPState (f i y) st')
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

End PState.