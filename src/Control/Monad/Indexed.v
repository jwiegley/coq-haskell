Require Import Hask.Ltac.
Require Import Hask.Prelude.
Require Import FunctionalExtensionality.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Even though we have the Category class in Category.v, the Functors
   and Monads I'm interested in reasoning about are all endofunctors on
   Coq, so there is no reason to carry around that extra machinery. *)

Class IFunctor (F : Type -> Type -> Type -> Type) :=
{ iobj := F
; imap : forall {I O X Y}, (X -> Y) -> F I O X -> F I O Y

; ifun_identity : forall {I O X}, @imap I O _ _ (@id X) = id
; ifun_composition : forall {I O X Y Z} (f : Y -> Z) (g : X -> Y),
    imap f \o imap g = @imap I O _ _ (f \o g)
}.

Arguments imap             [F] [IFunctor] [I O X] [Y] f g.
Arguments ifun_identity    {F} {IFunctor} {I O X}.
Arguments ifun_composition [F] [IFunctor] [I O X] [Y] [Z] f g.

Notation "f <$$> g" := (imap f g) (at level 28, left associativity).

Notation "imap[ M ]" := (@imap M _ _ _) (at level 9).
Notation "imap[ M N ]" := (@imap (fun X => M (N X)) _ _ _) (at level 9).
Notation "imap[ M N O ]" := (@imap (fun X => M (N (O X))) _ _ _) (at level 9).

Coercion iobj : IFunctor >-> Funclass.

(*
Lemma ifun_irrelevance `(F : IFunctor)
  : forall (f g : forall {I O X Y}, (X -> Y) -> (F I O X -> F I O Y))
           i i' c c',
  @f = @g ->
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
*)

Section IFunctors.

  Variable F : Type -> Type -> Type -> Type.
  Context `{IFunctor F}.

  Theorem ifun_identity_x : forall {I O X} (x : F I O X), imap id x = id x.
  Proof.
    intros.
    rewrite ifun_identity.
    reflexivity.
  Qed.

  Theorem ifun_composition_x
    : forall {I O X Y Z} (f : Y -> Z) (g : X -> Y) (x : F I O X),
    f <$$> (g <$$> x) = (f \o g) <$$> x.
  Proof.
    intros.
    rewrite <- ifun_composition.
    reflexivity.
  Qed.

End IFunctors.

Reserved Notation "f <**> g" (at level 28, left associativity).

Class IApplicative (F : Type -> Type -> Type -> Type) :=
{ is_ifunctor :> IFunctor F

; ipure : forall {I X}, X -> F I I X
; iap : forall {I J K X Y}, F I J (X -> Y) -> F J K X -> F I K Y
    where "f <**> g" := (iap f g)

; iapp_identity : forall {I X}, @iap _ _ I _ _ (@ipure I _ (@id X)) = id
; iapp_composition
    : forall {I J K L X Y Z}
             (u : F I J (Y -> Z)) (v : F J K (X -> Y)) (w : F K L X),
    ipure compose <**> u <**> v <**> w = u <**> (v <**> w)
; iapp_homomorphism : forall {I X Y} (x : X) (f : X -> Y),
    ipure f <**> ipure x = @ipure I _ (f x)
; iapp_interchange : forall {I J X Y} (y : X) (u : F I J (X -> Y)),
    u <**> ipure y = ipure (fun f => f y) <**> u

; app_imap_unit : forall {I O X Y} (f : X -> Y), iap (ipure f) = @imap _ _ I O _ _ f
}.

Notation "ipure[ M ]" := (@ipure M _ _) (at level 9).
Notation "ipure[ M N ]" := (@ipure (fun X => M (N X)) _ _) (at level 9).

Notation "iap[ M ]" := (@iap M _ _ _) (at level 9).
Notation "iap[ M N ]" := (@iap (fun X => M (N X)) _ _ _) (at level 9).
Notation "iap[ M N O ]" := (@iap (fun X => M (N (O X))) _ _ _) (at level 9).

Notation "f <**> g" := (iap f g) (at level 28, left associativity).

(* Notation "[| f x y .. z |]" := (.. (f <$$> x <**> y) .. <**> z) *)
(*     (at level 9, left associativity, f at level 9, *)
(*      x at level 9, y at level 9, z at level 9). *)

Definition iapp_merge {X Y Z W} (f : X -> Y) (g : Z -> W)
  (t : X * Z) : Y * W  :=
  match t with (x, z) => (f x, g z) end.

Definition iapp_prod {F : Type -> Type -> Type -> Type} `{IApplicative F}
  {I J K X Y} (x : F I J X) (y : F J K Y) : F I K (X * Y)%type :=
  pair <$$> x <**> y.

Notation "f *** g" := (iapp_merge f g) (at level 28, left associativity).

Notation "f ** g" := (iapp_prod f g) (at level 28, left associativity).

Ltac rewrite_iapp_homomorphisms :=
  (repeat (rewrite <- app_imap_unit);
   rewrite iapp_homomorphism;
   repeat (rewrite app_imap_unit)).

Section IApplicatives.

  Variable F : Type -> Type -> Type -> Type.
  Context `{IApplicative F}.

  Theorem app_imap_compose : forall I A B (f : A -> B),
    ipure \o f = @imap _ _ I I _ _ f \o @ipure _ _ I _.
  Proof.
    intros.
    extensionality x.
    unfold comp.
    rewrite <- iapp_homomorphism.
    rewrite app_imap_unit.
    reflexivity.
  Qed.

  Theorem app_imap_compose_x : forall I A B (f : A -> B) (x : A),
    ipure (f x) = imap f (@ipure _ _ I _ x).
  Proof.
    intros.
    assert (ipure (f x) = (@ipure _ _ I _ \o f) x).
      unfold comp. reflexivity.
    assert (imap f (ipure x) = (imap f \o @ipure _ _ I _) x).
      unfold comp. reflexivity.
    rewrite H0. rewrite H1.
    rewrite app_imap_compose.
    reflexivity.
  Qed.

  Theorem iapp_identity_x : forall {I X} {x : F I I X},
    iap (ipure (@id X)) x = id x.
  Proof.
    intros.
    rewrite app_imap_unit.
    apply ifun_identity_x.
  Qed.

  Theorem iapp_homomorphism_2
    : forall {I X Y Z} (x : X) (y : Y) (f : X -> Y -> Z),
    f <$$> ipure x <**> ipure y = @ipure _ _ I _ (f x y).
  Proof.
    intros.
    rewrite <- iapp_homomorphism.
    rewrite <- iapp_homomorphism.
    rewrite app_imap_unit.
    reflexivity.
  Qed.

  (* This theorem was given as an exercise by Brent Yorgey at:

     http://www.haskell.org/haskellwiki/Typeclassopedia#IApplicative
  *)
  Theorem iapp_flip : forall {J K X Y} (x : F J K X) (f : X -> Y),
    ipure f <**> x = ipure (flip apply) <**> x <**> ipure f.
  Proof.
    intros.
    rewrite iapp_interchange.
    rewrite <- iapp_composition.
    rewrite app_imap_unit.
    rewrite app_imap_unit.
    rewrite iapp_homomorphism_2.
    unfold comp.
    rewrite app_imap_unit.
    reflexivity.
  Qed.

  Definition iapp_unit : F unit unit unit := ipure tt.

  Theorem iapp_embed
    : forall {G : Type -> Type -> Type -> Type} `{IApplicative G}
             {I J K X Y} (x : G I J (X -> Y)) (y : G J K X),
    ipure (x <**> y) = ipure iap <**> ipure x <**> @ipure _ _ K _ y.
  Proof.
    intros.
    rewrite_iapp_homomorphisms.
    rewrite <- iapp_homomorphism.
    rewrite <- app_imap_unit.
    reflexivity.
  Qed.

(*
  Theorem iapp_split
    : forall I J K A B C (f : A -> B -> C) (x : F I J A) (y : F J K B),
    f <$$> x <**> y = uncurry f <$$> (x ** y).
  Proof.
    intros. unfold iapp_prod.
    repeat (rewrite <- app_imap_unit).
    repeat (rewrite <- iapp_composition; f_equal).
    repeat (rewrite iapp_homomorphism).
    unfold uncurry, compose. f_equal.
  Qed.
*)

  Theorem iapp_naturality
    : forall {I J K A B C D}
             (f : A -> C) (g : B -> D) (u : F I J A) (v : F J K B),
    imap (f *** g) (u ** v) = (imap f u) ** (imap g v).
  Proof.
    intros.
    unfold iapp_prod.
    rewrite <- app_imap_unit.
    rewrite ifun_composition_x.
    repeat (rewrite <- app_imap_unit).
    rewrite <- iapp_composition.
    rewrite <- iapp_composition.
    rewrite <- iapp_composition.
    rewrite <- iapp_composition.
    rewrite iapp_composition.
    rewrite iapp_composition.
    rewrite_iapp_homomorphisms.
    rewrite ifun_composition_x.
    rewrite ifun_composition_x.
    rewrite iapp_interchange.
    rewrite app_imap_unit.
    rewrite ifun_composition_x.
    unfold comp.
    reflexivity.
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

  Theorem app_right_identity `(v : F A) : (v ** ipure tt) ≡ v.
  Proof.
    intros.
    unfold app_prod, app_unit.
    rewrite <- app_imap_unit.
    rewrite app_interchange.
    rewrite <- app_composition.
    rewrite app_homomorphism.
    rewrite app_homomorphism.
    rewrite app_imap_unit.
    unfold comp.
    split.
      assert (imap (fun x : A => (x, tt)) =
              (@from (F (A * unit)) (F A)
                     (Functor_Isomorphism _ RTuple_Isomorphism))).
        reflexivity. rewrite H0.
      apply iso_from_x.
      reflexivity.
  Qed.
*)

(*
  Theorem iapp_embed_left_triple
    : forall I J K L A B C (u : F I J A) (v : F J K B) (w : F K L C),
    u ** v ** w = left_triple <$$> u <**> v <**> w.
  Proof.
    intros.
    unfold iapp_prod.
    repeat (rewrite <- app_imap_unit).
    rewrite <- iapp_composition.
    f_equal. f_equal.
    rewrite_iapp_homomorphisms.
    rewrite ifun_composition_x.
    reflexivity.
  Qed.

  Theorem iapp_embed_right_triple
    : forall I J K L A B C (u : F I J A) (v : F J K B) (w : F K L C),
    u ** (v ** w) = right_triple <$$> u <**> v <**> w.
  Proof.
    intros.
    unfold iapp_prod.
    repeat (rewrite <- app_imap_unit).
    rewrite <- iapp_composition.
    f_equal. f_equal.
    repeat (rewrite app_imap_unit).
    rewrite ifun_composition_x.
    repeat (rewrite <- app_imap_unit).
    rewrite <- iapp_composition.
    f_equal.
    repeat (rewrite app_imap_unit).
    rewrite ifun_composition_x.
    rewrite iapp_interchange.
    rewrite app_imap_unit.
    rewrite ifun_composition_x.
    unfold comp.
    reflexivity.
  Qed.
*)

(*
  Theorem iapp_associativity
    : forall A B C (u : F I J A) (v : F J K B) (w : F K L C),
    ((u ** v) ** w) ≡ (u ** (v ** w)).
  Proof.
    intros.
    rewrite iapp_embed_left_triple.
    rewrite iapp_embed_right_triple.
    split; simpl;
    repeat (rewrite <- app_imap_unit);
    rewrite <- iapp_composition;
    rewrite <- iapp_composition;
    rewrite <- iapp_composition;
    repeat f_equal;
    repeat (rewrite app_imap_unit);
    rewrite ifun_composition_x;
    rewrite ifun_composition_x;
    rewrite <- app_imap_compose_x;
    rewrite iapp_homomorphism;
    reflexivity.
  Qed.
*)

  Definition liftIA2 {I J K A B C} (f : A -> B -> C)
    (x : F I J A) (y : F J K B) : F I K C :=
    f <$$> x <**> y.

End IApplicatives.


Class IMonad (M : Type -> Type -> Type -> Type) :=
{ is_iapplicative :> IApplicative M

; ijoin : forall {I A O X}, M I A (M A O X) -> M I O X

; imonad_law_1 : forall {I O J K X},
    (@ijoin I J O X) \o imap ijoin = (@ijoin I K O X) \o (@ijoin I J K _)
; imonad_law_2 : forall {I X},
    ijoin \o @imap _ _ I _ _ _ (@ipure M is_iapplicative I X) = id
; imonad_law_3 : forall {I O X},
    (@ijoin _ _ O X) \o (@ipure _ _ I _) = id
; imonad_law_4 : forall {I O A X Y} (f : X -> Y),
    ijoin \o imap (imap f) = imap f \o (@ijoin I A O _)
}.

Notation "ijoin[ M ]" := (@ijoin M _ _ _ _ _) (at level 9).
Notation "ijoin[ M N ]" := (@ijoin (fun X => M (N X)) _ _ _ _ _) (at level 9).

Definition ibind {M : Type -> Type -> Type -> Type} `{IMonad M} {I J K X Y}
  (f : (X -> M J K Y)) (x : M I J X) : M I K Y :=
  @ijoin M _ I J K Y (@imap _ _ I J _ _ f x).

Declare Scope imonad_scope.
Delimit Scope imonad_scope with imonad.

Notation "m >>= f" := (ibind f m) (at level 42, right associativity) : imonad_scope.

Notation "X <- A ; B" := (A >>= (fun X => B))%imonad
  (at level 81, right associativity, only parsing) : imonad_scope.

Notation "A ;; B" := (A >>= (fun _ => B))%imonad
  (at level 42, right associativity, only parsing) : imonad_scope.

Open Scope imonad_scope.

Theorem imonad_law_1_x
  : forall M (m_dict : IMonad M) I J K O A (x : M I J (M J K (M K O A))),
  ijoin (imap ijoin x) = (@ijoin M m_dict _ _ _ A) (ijoin x).
Proof.
  intros.
  assert (ijoin (imap ijoin x) = (ijoin \o imap ijoin) x).
    unfold comp. reflexivity.
  assert (ijoin (ijoin x) = (ijoin \o ijoin) x).
    unfold comp. reflexivity.
  rewrite H. rewrite H0.
  rewrite imonad_law_1.
  reflexivity.
Qed.

Theorem imonad_law_2_x
  : forall M (m_dict : IMonad M) I A (x : M I I A),
  ijoin (@imap _ _ I I _ _ (@ipure M _ I A) x) = x.
Proof.
  intros.
  assert (ijoin (imap ipure x) = (ijoin \o imap ipure) x).
    unfold comp. reflexivity.
  rewrite H.
  rewrite imonad_law_2.
  reflexivity.
Qed.

Theorem imonad_law_3_x
  : forall M (m_dict : IMonad M) I A (x : M I I A),
  (@ijoin M m_dict _ _ _ A) (ipure x) = x.
Proof.
  intros.
  assert (ijoin (ipure x) = (ijoin \o ipure) x).
    unfold comp. reflexivity.
  rewrite H.
  rewrite imonad_law_3.
  reflexivity.
Qed.

Theorem imonad_law_4_x
  : forall M (m_dict : IMonad M)
      I J O A B (f : A -> B) (x : M I J (M J O A)),
  ijoin (imap (imap f) x) = imap f (ijoin x).
Proof.
  intros.
  assert (ijoin (imap (imap f) x) = (ijoin \o imap (imap f)) x).
    unfold comp. reflexivity.
  assert (imap f (ijoin x) = (imap f \o ijoin) x).
    unfold comp. reflexivity.
  rewrite H. rewrite H0.
  rewrite imonad_law_4.
  reflexivity.
Qed.

Theorem imonad_assoc : forall M `{IMonad M}
  {I J K L A B C} (m : M I J A) (f : A -> M J K B) (g : B -> M K L C),
  (m >>= f) >>= g = m >>= (fun x => f x >>= g).
Proof.
  intros.
  unfold ibind.
  rewrite <- imonad_law_4_x.
  rewrite ifun_composition_x.
  rewrite <- imonad_law_1_x.
  rewrite ifun_composition_x.
  f_equal.
Qed.

Inductive IState (i o a : Type) := mkIState : (i -> (a * o)) -> IState i o a.

Arguments mkIState [i o a] _.

Definition runIState {i o a} (x : IState i o a) :=
  match x with mkIState f => f end.

#[export]
Program Instance IState_IFunctor : IFunctor IState := {
    imap := fun _ _ _ _ f x =>
      mkIState (fun st => let (a,st') := runIState x st in (f a, st'))
}.
Obligation 1.
  extensionality x.
  destruct x.
  unfold id.
  f_equal.
  extensionality st.
  simpl.
  destruct (p st).
  reflexivity.
Qed.
Obligation 2.
  extensionality x.
  unfold comp.
  f_equal.
  extensionality y.
  destruct x.
  simpl.
  destruct (p y).
  reflexivity.
Qed.

Definition iget  {i}     : IState i i i := mkIState (fun i => (i, i)).
Definition igets {i a} f : IState i i a := mkIState (fun s => (f s, s)).

Definition iput {i o} (x : o) : IState i o unit := mkIState (fun s => (tt, x)).

Definition imodify {i o} (f : i -> o) : IState i o unit :=
  mkIState (fun i => (tt, f i)).

#[export]
Program Instance IState_IApplicative : IApplicative IState := {
    ipure := fun _ _ x => mkIState (fun st => (x, st));
    iap := fun _ _ _ _ _ f x =>
      mkIState (fun st =>
        let (f', st') := runIState f st in
        let (x', st'') := runIState x st' in
        (f' x', st''))
}.
Obligation 1.
  extensionality x.
  destruct x. compute.
  f_equal.
  extensionality st.
  destruct (p st).
  reflexivity.
Qed.
Obligation 2.
  destruct u.
  destruct v.
  destruct w. simpl.
  f_equal.
  extensionality st.
  destruct (p st).
  destruct (p0 j).
  destruct (p1 k).
  reflexivity.
Qed.

#[export]
Program Instance IState_IMonad : IMonad IState := {
    ijoin := fun _ _ _ _ x => mkIState (fun st =>
      let (y, st') := runIState x st in
      let (a, st'') := runIState y st' in
      (a, st''))
}.
Obligation 1.
  extensionality x.
  unfold comp.
  f_equal.
  extensionality y.
  destruct x. simpl.
  destruct (p y).
  destruct i. simpl.
  destruct (p0 j).
  destruct i. simpl.
  destruct (p1 k).
  reflexivity.
Qed.
Obligation 2.
  extensionality x.
  unfold comp, id.
  destruct x.
  f_equal. simpl.
  extensionality y.
  destruct (p y).
  reflexivity.
Qed.
Obligation 3.
  extensionality x.
  unfold comp, id.
  destruct x. simpl.
  f_equal.
  extensionality y.
  destruct (p y).
  reflexivity.
Qed.
Obligation 4.
  extensionality x.
  unfold comp.
  f_equal.
  extensionality y.
  destruct x. simpl.
  destruct (p y). simpl.
  destruct i. simpl.
  destruct (p0 a).
  reflexivity.
Qed.
