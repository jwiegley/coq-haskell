Require Export RApplicative.

Class RMonad {a : Type} (M : a -> a -> relation a -> Type -> Type) :=
{ is_rapplicative :> RApplicative M

; rjoin : forall {I A O X}, P A A -> M I A (M A O X) -> M I O X

; rmonad_law_1 : forall {I O J K X} (S : P J J) (T : P K K),
    (@rjoin I J O X S) ∘ rmap (rjoin T) = (@rjoin I K O X T) ∘ (@rjoin I J K _ S)
; rmonad_law_2 : forall {I X} (S : P I I),
    rjoin S ∘ @rmap _ _ _ I _ _ _ (@rpure _ M _ is_rapplicative I X) = id
; rmonad_law_3 : forall {I O X} (S : P I I),
    (@rjoin _ _ O X S) ∘ (@rpure _ _ _ _ I _) = id
; rmonad_law_4 : forall {I O A X Y} (S : P A A) (f : X -> Y),
    rjoin S ∘ rmap (rmap f) = rmap f ∘ (@rjoin I A O _ S)
}.

Notation "rjoin/ M" := (@rjoin M _ _ _ _ _) (at level 28).
Notation "rjoin/ M N" := (@rjoin (fun X => M (N X)) _ _ _ _ _) (at level 26).

Definition ibind {M : Type -> Type -> Type -> Type} `{Rmonad M} {I J K X Y}
  (f : (X -> M J K Y)) (x : M I J X) : M I K Y :=
  @rjoin M _ I J K Y (@rmap _ _ I J _ _ f x).

Notation "m >>>= f" := (ibind f m) (at level 25, left associativity).

(* Notation "x <- c1 ;; c2" := (@ibind _ _ _ _ _ c1 (fun x => c2)) *)
(*   (at level 100, c1 at next level, right associativity). *)

Notation "X <<- A ; B" := (A >>>= (fun X => B))
  (right associativity, at level 84, A1 at next level).

(* Notation "x : a <== c1 ;; c2" := (@ibind _ _ _ _ _ c1 (fun x : a => c2)) *)
(*   (at level 100, c1 at next level, right associativity). *)

Notation "A ;;; B" := (_ <<- A ; B)
  (right associativity, at level 84, A1 at next level).

Theorem rmonad_law_1_x
  : forall M (m_dict : Rmonad M) I J K O A (x : M I J (M J K (M K O A))),
  rjoin (rmap rjoin x) = (@rjoin M m_dict _ _ _ A) (rjoin x).
Proof.
  intros.
  assert (rjoin (rmap rjoin x) = (rjoin ∘ rmap rjoin) x).
    unfold compose. reflexivity.
  assert (rjoin (rjoin x) = (rjoin ∘ rjoin) x).
    unfold compose. reflexivity.
  rewrite H. rewrite H0.
  rewrite rmonad_law_1.
  reflexivity.
Qed.

Theorem rmonad_law_2_x
  : forall M (m_dict : Rmonad M) I A (x : M I I A),
  rjoin (@rmap _ _ I I _ _ (@rpure M _ I A) x) = x.
Proof.
  intros.
  assert (rjoin (rmap rpure x) = (rjoin ∘ rmap rpure) x).
    unfold compose. reflexivity.
  rewrite H.
  rewrite rmonad_law_2.
  reflexivity.
Qed.

Theorem rmonad_law_3_x
  : forall M (m_dict : Rmonad M) I A (x : M I I A),
  (@rjoin M m_dict _ _ _ A) (rpure x) = x.
Proof.
  intros.
  assert (rjoin (rpure x) = (rjoin ∘ rpure) x).
    unfold compose. reflexivity.
  rewrite H.
  rewrite rmonad_law_3.
  reflexivity.
Qed.

Theorem rmonad_law_4_x
  : forall M (m_dict : Rmonad M)
      I J O A B (f : A -> B) (x : M I J (M J O A)),
  rjoin (rmap (rmap f) x) = rmap f (rjoin x).
Proof.
  intros.
  assert (rjoin (rmap (rmap f) x) = (rjoin ∘ rmap (rmap f)) x).
    unfold compose. reflexivity.
  assert (rmap f (rjoin x) = (rmap f ∘ rjoin) x).
    unfold compose. reflexivity.
  rewrite H. rewrite H0.
  rewrite rmonad_law_4.
  reflexivity.
Qed.

Theorem monad_assoc : forall M `{Rmonad M}
  {I J K L A B C} (m : M I J A) (f : A -> M J K B) (g : B -> M K L C),
  m >>>= f >>>= g = m >>>= (fun x => f x >>>= g).
Proof.
  intros.
  unfold ibind.
  rewrite <- rmonad_law_4_x.
  rewrite ifun_composition_x.
  rewrite <- rmonad_law_1_x.
  rewrite ifun_composition_x.
  f_equal.
Qed.
