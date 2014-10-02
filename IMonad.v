Require Export IApplicative.

Class IMonad (M : Type -> Type -> Type -> Type) :=
{ is_iapplicative :> IApplicative M

; ijoin : forall {I A O X}, M I A (M A O X) -> M I O X

  (* x : M I J (M J K (M K O A)) *)

; imonad_law_1 : forall {I O J K X},
    (@ijoin I J O X) ∘ imap ijoin = (@ijoin I K O X) ∘ (@ijoin I J K _)
; imonad_law_2 : forall {I X},
    ijoin ∘ @imap _ _ I _ _ _ (@ipure M is_iapplicative I X) = id
; imonad_law_3 : forall {I O X},
    (@ijoin _ _ O X) ∘ (@ipure _ _ I _) = id
; imonad_law_4 : forall {I O A X Y} (f : X -> Y),
    ijoin ∘ imap (imap f) = imap f ∘ (@ijoin I A O _)
}.

Notation "ijoin/ M" := (@ijoin M _ _ _ _ _) (at level 28).
Notation "ijoin/ M N" := (@ijoin (fun X => M (N X)) _ _ _ _ _) (at level 26).

Definition ibind {M} `{IMonad M} {I J K X Y}
  (f : (X -> M J K Y)) (x : M I J X) : M I K Y := ijoin (imap f x).

Notation "m >>>= f" := (ibind f m) (at level 25, left associativity).

(* Notation "x <- c1 ;; c2" := (@ibind _ _ _ _ _ c1 (fun x => c2)) *)
(*   (at level 100, c1 at next level, right associativity). *)

Notation "X <<- A ; B" := (A >>>= (fun X => B))
  (right associativity, at level 84, A1 at next level).

(* Notation "x : a <== c1 ;; c2" := (@ibind _ _ _ _ _ c1 (fun x : a => c2)) *)
(*   (at level 100, c1 at next level, right associativity). *)

Notation "A ;;; B" := (_ <<- A ; B)
  (right associativity, at level 84, A1 at next level).

Theorem imonad_law_1_x
  : forall M (m_dict : IMonad M) I J K O A (x : M I J (M J K (M K O A))),
  ijoin (imap ijoin x) = (@ijoin M m_dict _ _ _ A) (ijoin x).
Proof.
  intros.
  assert (ijoin (imap ijoin x) = (ijoin ∘ imap ijoin) x).
    unfold compose. reflexivity.
  assert (ijoin (ijoin x) = (ijoin ∘ ijoin) x).
    unfold compose. reflexivity.
  rewrite H. rewrite H0.
  rewrite imonad_law_1.
  reflexivity.
Qed.

Theorem imonad_law_2_x
  : forall M (m_dict : IMonad M) I A (x : M I I A),
  ijoin (@imap _ _ I I _ _ (@ipure M _ I A) x) = x.
Proof.
  intros.
  assert (ijoin (imap ipure x) = (ijoin ∘ imap ipure) x).
    unfold compose. reflexivity.
  rewrite H.
  rewrite imonad_law_2.
  reflexivity.
Qed.

Theorem imonad_law_3_x
  : forall M (m_dict : IMonad M) I A (x : M I I A),
  (@ijoin M m_dict _ _ _ A) (ipure x) = x.
Proof.
  intros.
  assert (ijoin (ipure x) = (ijoin ∘ ipure) x).
    unfold compose. reflexivity.
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
  assert (ijoin (imap (imap f) x) = (ijoin ∘ imap (imap f)) x).
    unfold compose. reflexivity.
  assert (imap f (ijoin x) = (imap f ∘ ijoin) x).
    unfold compose. reflexivity.
  rewrite H. rewrite H0.
  rewrite imonad_law_4.
  reflexivity.
Qed.

Theorem monad_assoc : forall M `{IMonad M}
  {I J K L A B C} (m : M I J A) (f : A -> M J K B) (g : B -> M K L C),
  m >>>= f >>>= g = m >>>= (fun x => f x >>>= g).
Proof.
  intros.
  unfold ibind.
  rewrite <- imonad_law_4_x.
  rewrite ifun_composition_x.
  rewrite <- imonad_law_1_x.
  rewrite ifun_composition_x.
  f_equal.
Qed.
