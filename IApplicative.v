Require Export IEndo.
Require Export Tuple.
Require Export Coq.Lists.List.

Generalizable All Variables.

Reserved Notation "f <**> g" (at level 28, left associativity).

Class IApplicative (F : Type -> Type -> Type -> Type) :=
{ is_ifunctor :> IFunctor F

; ipure : forall {I X}, X -> F I I X
; iap : forall {I J K X Y}, F I J (X -> Y) -> F J K X -> F I K Y
    where "f <**> g" := (iap f g)

(*
; iapp_identity : forall {X}, iap (ipure (@id X)) = id
; iapp_composition
    : forall {I J K X Y Z} (v : F (X -> Y)) (u : F (Y -> Z)) (w : F X),
    ipure compose <**> u <**> v <**> w = u <**> (v <**> w)
*)
; iapp_homomorphism : forall {I X Y} (x : X) (f : X -> Y),
    ipure f <**> ipure x = @ipure I _ (f x)
(*
; iapp_interchange : forall {X Y} (y : X) (u : F (X -> Y)),
    u <**> ipure y = ipure (fun f => f y) <**> u
*)

; app_imap_unit : forall {I O X Y} (f : X -> Y), iap (ipure f) = @imap _ _ I O _ _ f
}.

Notation "ipure/ M" := (@ipure M _ _) (at level 28).
Notation "ipure/ M N" := (@ipure (fun X => M (N X)) _ _) (at level 26).

Notation "iap[ M ]  f" := (@iap M _ _ _ f) (at level 28).
Notation "iap[ M N ]  f" := (@iap (fun X => M (N X)) _ _ _ f) (at level 26).
Notation "iap[ M N O ]  f" := (@iap (fun X => M (N (O X))) _ _ _ f) (at level 24).

Notation "f <**> g" := (iap f g) (at level 28, left associativity).

Notation "[| f x y .. z |]" := (.. (f <$$> x <**> y) .. <**> z)
    (at level 9, left associativity, f at level 9,
     x at level 9, y at level 9, z at level 9).

Definition app_merge {X Y Z W} (f : X -> Y) (g : Z -> W)
  (t : X * Z) : Y * W  :=
  match t with (x, z) => (f x, g z) end.

Definition app_prod {F : Type -> Type -> Type -> Type} `{IApplicative F}
  {I J K X Y} (x : F I J X) (y : F J K Y) : F I K (X * Y) := pair <$$> x <**> y.

Notation "f *** g" := (app_merge f g) (at level 28, left associativity).

Notation "f ** g" := (app_prod f g) (at level 28, left associativity).

Ltac rewrite_app_homomorphisms :=
  (repeat (rewrite <- app_imap_unit);
   rewrite iapp_homomorphism;
   repeat (rewrite app_imap_unit)).

Section IApplicatives.

  Variable F : Type -> Type -> Type -> Type.
  Context `{IApplicative F}.

  Theorem app_imap_compose : forall I A B (f : A -> B),
    ipure ∘ f = @imap _ _ I I _ _ f ∘ @ipure _ _ I _.
  Proof.
    intros.
    extensionality x.
    unfold compose.
    rewrite <- iapp_homomorphism.
    rewrite app_imap_unit.
    reflexivity.
  Qed.

  Theorem app_imap_compose_x : forall I A B (f : A -> B) (x : A),
    ipure (f x) = imap f (@ipure _ _ I _ x).
  Proof.
    intros.
    assert (ipure (f x) = (@ipure _ _ I _ ∘ f) x).
      unfold compose. reflexivity.
    assert (imap f (ipure x) = (imap f ∘ @ipure _ _ I _) x).
      unfold compose. reflexivity.
    rewrite H0. rewrite H1.
    rewrite app_imap_compose.
    reflexivity.
  Qed.

  Theorem app_identity_x : forall {I X} {x : F I I X},
    iap (ipure (@id X)) x = id x.
  Proof.
    intros.
    rewrite app_imap_unit.
    apply ifun_identity_x.
  Qed.

  Theorem app_homomorphism_2 : forall {I X Y Z} (x : X) (y : Y) (f : X -> Y -> Z),
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
(*
  Theorem app_flip : forall {J K X Y} (x : F J K X) (f : X -> Y),
    ipure f <**> x = ipure (flip apply) <**> x <**> ipure f.
  Proof.
    intros.
    rewrite iapp_interchange.
    rewrite <- iapp_composition.
    rewrite app_imap_unit.
    rewrite app_imap_unit.
    rewrite app_homomorphism_2.
    unfold compose.
    rewrite app_imap_unit.
    reflexivity.
  Qed.
*)

  Definition app_unit : F unit unit unit := ipure tt.

  Theorem app_embed : forall {G : Type -> Type -> Type -> Type} `{IApplicative G}
      {I J K X Y} (x : G I J (X -> Y)) (y : G J K X),
    ipure (x <**> y) = ipure iap <**> ipure x <**> @ipure _ _ K _ y.
  Proof.
    intros.
    rewrite_app_homomorphisms.
    rewrite <- iapp_homomorphism.
    rewrite <- app_imap_unit.
    reflexivity.
  Qed.

(*
  Theorem app_split : forall I J K A B C (f : A -> B -> C) (x : F I J A) (y : F J K B),
    f <$$> x <**> y = uncurry f <$$> (x ** y).
  Proof.
    intros. unfold app_prod.
    repeat (rewrite <- app_imap_unit).
    repeat (rewrite <- app_composition; f_equal).
    repeat (rewrite app_homomorphism).
    unfold uncurry, compose. f_equal.
  Qed.

  Theorem app_naturality
    : forall {I J K A B C D} (f : A -> C) (g : B -> D) (u : F I J A) (v : F J K B),
    imap (f *** g) (u ** v) = (imap f u) ** (imap g v).
  Proof.
    intros.
    unfold app_prod.
    rewrite <- app_imap_unit.
    rewrite fun_composition_x.
    repeat (rewrite <- app_imap_unit).
    rewrite <- app_composition.
    rewrite <- app_composition.
    rewrite <- app_composition.
    rewrite <- app_composition.
    rewrite app_composition.
    rewrite app_composition.
    f_equal.
    rewrite_app_homomorphisms.
    rewrite fun_composition_x.
    rewrite fun_composition_x.
    rewrite app_interchange.
    rewrite app_imap_unit.
    rewrite fun_composition_x.
    f_equal.
  Qed.
*)

(*
  Theorem app_left_identity `(v : F A) : (F unit * v) ≅ v.
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
    unfold compose.
    split.
      assert (imap (fun x : A => (x, tt)) =
              (@from (F (A * unit)) (F A)
                     (Functor_Isomorphism _ RTuple_Isomorphism))).
        reflexivity. rewrite H0.
      apply iso_from_x.
      reflexivity.
  Qed.

  Theorem app_embed_left_triple : forall A B C (u : F A) (v : F B) (w : F C),
    u ** v ** w = left_triple <$$> u <**> v <**> w.
  Proof.
    intros.
    unfold app_prod.
    repeat (rewrite <- app_imap_unit).
    rewrite <- app_composition.
    f_equal. f_equal.
    rewrite_app_homomorphisms.
    rewrite fun_composition_x.
    reflexivity.
  Qed.

  Theorem app_embed_right_triple : forall A B C (u : F A) (v : F B) (w : F C),
    u ** (v ** w) = right_triple <$$> u <**> v <**> w.
  Proof.
    intros.
    unfold app_prod.
    repeat (rewrite <- app_imap_unit).
    rewrite <- app_composition.
    f_equal. f_equal.
    repeat (rewrite app_imap_unit).
    rewrite fun_composition_x.
    repeat (rewrite <- app_imap_unit).
    rewrite <- app_composition.
    f_equal.
    repeat (rewrite app_imap_unit).
    rewrite fun_composition_x.
    rewrite app_interchange.
    rewrite app_imap_unit.
    rewrite fun_composition_x.
    unfold compose.
    reflexivity.
  Qed.
*)

(*
  Theorem app_associativity : forall A B C (u : F A) (v : F B) (w : F C),
    ((u ** v) ** w) ≡ (u ** (v ** w)).
  Proof.
    intros.
    rewrite app_embed_left_triple.
    rewrite app_embed_right_triple.
    split; simpl;
    repeat (rewrite <- app_imap_unit);
    rewrite <- app_composition;
    rewrite <- app_composition;
    rewrite <- app_composition;
    repeat f_equal;
    repeat (rewrite app_imap_unit);
    rewrite fun_composition_x;
    rewrite fun_composition_x;
    rewrite <- app_imap_compose_x;
    rewrite app_homomorphism;
    reflexivity.
  Qed.
*)

  Definition liftIA2 {I J K A B C} (f : A -> B -> C)
    (x : F I J A) (y : F J K B) : F I K C :=
    f <$$> x <**> y.

End IApplicatives.
