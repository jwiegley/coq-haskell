Require Export Endo.
Require Import Tuple.
Require Import Coq.Lists.List.

Generalizable All Variables.

Reserved Notation "f <*> g" (at level 28, left associativity).

Class Applicative (F : Type -> Type) :=
{ is_functor :> Functor F

; pure : forall {X}, X -> F X
; ap : forall {X Y}, F (X -> Y) -> F X -> F Y
    where "f <*> g" := (ap f g)

; app_identity : forall {X}, ap (pure (@id X)) = id
; app_composition
    : forall {X Y Z} (v : F (X -> Y)) (u : F (Y -> Z)) (w : F X),
    pure compose <*> u <*> v <*> w = u <*> (v <*> w)
; app_homomorphism : forall {X Y} (x : X) (f : X -> Y),
    pure f <*> pure x = pure (f x)
; app_interchange : forall {X Y} (y : X) (u : F (X -> Y)),
    u <*> pure y = pure (fun f => f y) <*> u

; app_fmap_unit : forall {X Y} (f : X -> Y), ap (pure f) = fmap f
}.

Notation "pure/ M" := (@pure M _ _) (at level 28).
Notation "pure/ M N" := (@pure (fun X => M (N X)) _ _) (at level 26).

Notation "ap[ M ]  f" := (@ap M _ _ _ f) (at level 28).
Notation "ap[ M N ]  f" := (@ap (fun X => M (N X)) _ _ _ f) (at level 26).
Notation "ap[ M N O ]  f" := (@ap (fun X => M (N (O X))) _ _ _ f) (at level 24).

Notation "f <*> g" := (ap f g) (at level 28, left associativity).

Notation "[| f x y .. z |]" := (.. (f <$> x <*> y) .. <*> z)
    (at level 9, left associativity, f at level 9,
     x at level 9, y at level 9, z at level 9).

Definition app_merge {X Y Z W} (f : X -> Y) (g : Z -> W)
  (t : X * Z) : Y * W  :=
  match t with (x, z) => (f x, g z) end.

Definition app_prod {F : Type -> Type} `{Applicative F}
  {X Y} (x : F X) (y : F Y) : F (X * Y) := pair <$> x <*> y.

Notation "f *** g" := (app_merge f g) (at level 28, left associativity).

Notation "f ** g" := (app_prod f g) (at level 28, left associativity).

Ltac rewrite_app_homomorphisms :=
  (repeat (rewrite <- app_fmap_unit);
   rewrite app_homomorphism;
   repeat (rewrite app_fmap_unit)).

Section Applicatives.

  Variable F : Type -> Type.
  Context `{Applicative F}.

  Theorem app_fmap_compose : forall A B (f : A -> B),
    pure ∘ f = fmap f ∘ pure.
  Proof.
    intros.
    extensionality x.
    unfold compose.
    rewrite <- app_homomorphism.
    rewrite app_fmap_unit.
    reflexivity.
  Qed.

  Theorem app_fmap_compose_x : forall A B (f : A -> B) (x : A),
    pure (f x) = fmap f (pure x).
  Proof.
    intros.
    assert (pure (f x) = (pure ∘ f) x).
      unfold compose. reflexivity.
    assert (fmap f (pure x) = (fmap f ∘ pure) x).
      unfold compose. reflexivity.
    rewrite H0. rewrite H1.
    rewrite app_fmap_compose.
    reflexivity.
  Qed.

  Theorem app_identity_x : forall {X} {x : F X},
    ap (pure (@id X)) x = id x.
  Proof.
    intros.
    rewrite app_fmap_unit.
    apply fun_identity_x.
  Qed.

  Theorem app_homomorphism_2 : forall {X Y Z} (x : X) (y : Y) (f : X -> Y -> Z),
    f <$> pure x <*> pure y = pure (f x y).
  Proof.
    intros.
    rewrite <- app_homomorphism.
    rewrite <- app_homomorphism.
    rewrite app_fmap_unit.
    reflexivity.
  Qed.

  (* This theorem was given as an exercise by Brent Yorgey at:

     http://www.haskell.org/haskellwiki/Typeclassopedia#Applicative
  *)
  Theorem app_flip : forall {X Y} (x : F X) (f : X -> Y),
    pure f <*> x = pure (flip apply) <*> x <*> pure f.
  Proof.
    intros.
    rewrite app_interchange.
    rewrite <- app_composition.
    rewrite app_fmap_unit.
    rewrite app_fmap_unit.
    rewrite app_homomorphism_2.
    unfold compose.
    rewrite app_fmap_unit.
    reflexivity.
  Qed.

  Definition app_unit : F unit := pure tt.

  Theorem app_embed : forall {G : Type -> Type} `{Applicative G}
      {X Y} (x : G (X -> Y)) (y : G X),
    pure (x <*> y) = pure ap <*> pure x <*> pure y.
  Proof.
    intros.
    rewrite_app_homomorphisms.
    rewrite <- app_homomorphism.
    rewrite <- app_fmap_unit.
    reflexivity.
  Qed.

  Theorem app_split : forall A B C (f : A -> B -> C) (x : F A) (y : F B),
    f <$> x <*> y = uncurry f <$> (x ** y).
  Proof.
    intros. unfold app_prod.
    repeat (rewrite <- app_fmap_unit).
    repeat (rewrite <- app_composition; f_equal).
    repeat (rewrite app_homomorphism).
    unfold uncurry, compose. f_equal.
  Qed.

  Theorem app_naturality
    : forall {A B C D} (f : A -> C) (g : B -> D) (u : F A) (v : F B),
    fmap (f *** g) (u ** v) = (fmap f u) ** (fmap g v).
  Proof.
    intros.
    unfold app_prod.
    rewrite <- app_fmap_unit.
    rewrite fun_composition_x.
    repeat (rewrite <- app_fmap_unit).
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
    rewrite app_fmap_unit.
    rewrite fun_composition_x.
    f_equal.
  Qed.

(*
  Theorem app_left_identity `(v : F A) : (F unit * v) ≅ v.
  Proof.
    intros.
    unfold app_prod, app_unit.
    rewrite_app_homomorphisms.
    split.
      assert (fmap (pair tt) =
              (@from (F (unit * A)) (F A)
                     (Functor_Isomorphism _ LTuple_Isomorphism))).
        reflexivity. rewrite H0. clear H0.
      apply iso_from_x.
      reflexivity.
  Qed.

  Theorem app_right_identity `(v : F A) : (v ** pure tt) ≡ v.
  Proof.
    intros.
    unfold app_prod, app_unit.
    rewrite <- app_fmap_unit.
    rewrite app_interchange.
    rewrite <- app_composition.
    rewrite app_homomorphism.
    rewrite app_homomorphism.
    rewrite app_fmap_unit.
    unfold compose.
    split.
      assert (fmap (fun x : A => (x, tt)) =
              (@from (F (A * unit)) (F A)
                     (Functor_Isomorphism _ RTuple_Isomorphism))).
        reflexivity. rewrite H0.
      apply iso_from_x.
      reflexivity.
  Qed.
*)

  Theorem app_embed_left_triple : forall A B C (u : F A) (v : F B) (w : F C),
    u ** v ** w = left_triple <$> u <*> v <*> w.
  Proof.
    intros.
    unfold app_prod.
    repeat (rewrite <- app_fmap_unit).
    rewrite <- app_composition.
    f_equal. f_equal.
    rewrite_app_homomorphisms.
    rewrite fun_composition_x.
    reflexivity.
  Qed.

  Theorem app_embed_right_triple : forall A B C (u : F A) (v : F B) (w : F C),
    u ** (v ** w) = right_triple <$> u <*> v <*> w.
  Proof.
    intros.
    unfold app_prod.
    repeat (rewrite <- app_fmap_unit).
    rewrite <- app_composition.
    f_equal.
    repeat (rewrite app_fmap_unit).
    rewrite fun_composition_x.
    repeat (rewrite <- app_fmap_unit).
    rewrite <- app_composition.
    f_equal.
    repeat (rewrite app_fmap_unit).
    rewrite fun_composition_x.
    rewrite app_interchange.
    rewrite app_fmap_unit.
    rewrite fun_composition_x.
    unfold compose.
    reflexivity.
  Qed.

(*
  Theorem app_associativity : forall A B C (u : F A) (v : F B) (w : F C),
    ((u ** v) ** w) ≡ (u ** (v ** w)).
  Proof.
    intros.
    rewrite app_embed_left_triple.
    rewrite app_embed_right_triple.
    split; simpl;
    repeat (rewrite <- app_fmap_unit);
    rewrite <- app_composition;
    rewrite <- app_composition;
    rewrite <- app_composition;
    repeat f_equal;
    repeat (rewrite app_fmap_unit);
    rewrite fun_composition_x;
    rewrite fun_composition_x;
    rewrite <- app_fmap_compose_x;
    rewrite app_homomorphism;
    reflexivity.
  Qed.
*)

  Definition liftA2 {A B C} (f : A -> B -> C) (x : F A) (y : F B) : F C :=
    f <$> x <*> y.

End Applicatives.

#[export]
Program Instance option_Applicative : Applicative option := {
    pure := Some;
    ap := fun _ _ f x => match f with
      | None => None
      | Some f' => match x with
         | None => None
         | Some x' => Some (f' x')
         end
      end
}.
Obligation 1. extensionality x. destruct x; auto. Qed.
Obligation 2. destruct u; destruct v; destruct w; auto. Qed.

Module Import LN := ListNotations.

Fixpoint concat {a} (l : list (list a)) : list a :=
  match l with
  | nil => nil
  | x :: xs => x ++ concat xs
  end.

Fixpoint list_ap {a b} (fs : list (a -> b)) (xs : list a) : list b :=
  match fs with
  | nil => nil
  | f :: fs' => fmap f xs ++ list_ap fs' xs
  end.

#[export]
Program Instance list_Applicative : Applicative list := {
    pure := fun _ x => [x];
    ap := @list_ap
}.
Obligation 1.
  extensionality l.
  unfold id.
  rewrite app_nil_r.
  induction l; simpl. auto.
  congruence.
Qed.
Obligation 2.
Admitted.
Obligation 4.
  induction u. reflexivity.
  simpl in *. rewrite IHu.
  reflexivity.
Qed.
Obligation 5.
  extensionality l.
  rewrite app_nil_r.
  reflexivity.
Qed.
