Require Export Monad.
Require Export ACompose.
Require Coq.Setoids.Setoid.

Class Monad_Distributes (M : Type -> Type) (N : Type -> Type)
  `{Monad M} `{Applicative N} :=
{ prod : forall {A : Type}, N (M (N A)) -> M (N A)
; prod_law_1 : forall {A B : Type} (f : A -> B),
    prod ∘ fmap[N] (@fmap (fun X => M (N X)) _ _ _ f) =
    (@fmap (fun X => M (N X)) _ _ _ f) ∘ prod
; prod_law_2 : forall {A : Type}, (@prod A) ∘ eta/N = id
; prod_law_3 : forall {A : Type},
    prod ∘ fmap[N] (@eta (fun X => M (N X)) _ A) = eta/M
; prod_law_4 : forall {A : Type},
    prod ∘ fmap[N] (mu/M ∘ fmap[M] prod) =
    mu/M ∘ fmap[M] prod ∘ (@prod (M (N A)))
}.

(* These proofs are due to Mark P. Jones and Luc Duponcheel in their article
   "Composing monads", Research Report YALEU/DCS/RR-1004, December 1993.

   Given any Monad M, and any Premonad N (i.e., having eta), and further given
   an operation [prod] and its accompanying four laws, it can be shown that M
   N is closed under composition.
*)
Global Instance Monad_Compose (M : Type -> Type) (N : Type -> Type)
  `{Monad M} `{Applicative N} `{Monad_Distributes M N}
  : Monad (fun X => M (N X)) :=
{ is_applicative := Applicative_Compose M N
; mu := fun A => mu/M ∘ fmap[M] (@prod M N _ _ _ A)
}.
Proof.
  - (* monad_law_1 *) intros.
    rewrite <- comp_assoc with (f := mu/M).
    rewrite <- comp_assoc with (f := mu/M).
    rewrite comp_assoc with (f := fmap[M] (@prod M N _ _ _ X)).
    rewrite <- monad_law_4.
    rewrite <- comp_assoc.
    rewrite comp_assoc with (f := mu/M).
    rewrite comp_assoc with (f := mu/M).
    rewrite <- monad_law_1.
    repeat (rewrite <- comp_assoc).
    repeat (rewrite fun_composition).
    rewrite <- prod_law_4.
    repeat (rewrite <- fun_composition).
    unfold compose_fmap. reflexivity.

  - (* monad_law_2 *) intros.
    rewrite <- monad_law_2.
    rewrite <- prod_law_3. simpl.
    repeat (rewrite <- comp_assoc).
    repeat (rewrite <- fun_composition).
    unfold compose_fmap. reflexivity.

  - (* monad_law_3 *) intros.
    rewrite <- prod_law_2.
    rewrite <- comp_id_left.
    rewrite <- (@monad_law_3 M _ (N X)).
    rewrite <- comp_assoc.
    rewrite <- comp_assoc.
    rewrite app_fmap_compose. simpl.
    rewrite <- fun_composition.
    rewrite <- comp_assoc.
    unfold compose_eta.
    rewrite <- app_fmap_compose.
    reflexivity.

  - (* monad_law_4 *) intros. simpl.
    unfold compose_fmap.
    unfold compose at 3.
    unfold compose at 3.
    unfold compose at 4.
    rewrite comp_assoc at 1.
    rewrite <- monad_law_4.
    repeat (rewrite <- comp_assoc).
    rewrite fun_composition.
    rewrite fun_composition.
    pose proof (@prod_law_1 M N _ _ _ X).
    simpl in H4.
    unfold compose_fmap in H4.
    unfold compose in H4 at 2.
    unfold compose in H4 at 3.
    rewrite <- H4.
    reflexivity.
Defined.

(*--------------------------------------------------------------------------*)


Inductive Identity {a : Type} := Identity_ : a -> Identity.

Program Instance Identity_Functor : Functor (@Identity) := {
    fmap := fun _ _ f x => match x with Identity_ x' => Identity_ (f x') end
}.
Obligation 1. Admitted.
Obligation 2. Admitted.

Program Instance Identity_Applicative : Applicative (@Identity) := {
    eta := fun _ => Identity_;
    apply := fun _ _ mf mx => match mf with
        Identity_ f => match mx with
          Identity_ x => Identity_ (f x)
        end
      end
}.
Obligation 1. Admitted.
Obligation 2. Admitted.

Inductive Compose {f g : Type -> Type} {a : Type} :=
  Compose_ : f (g a) -> Compose.

Definition getCompose {f g : Type -> Type} {a : Type} (x : @Compose f g a) :
  f (g a) := match x with Compose_ x' => x' end.

Program Instance Compose_Functor
  {f g : Type -> Type} `{Functor f} `{Functor g} :
  Functor (@Compose f g) := {
    fmap := fun _ _ f x => match x with
        Compose_ k => Compose_ (fmap (fmap f) k)
      end
}.
Obligation 1. Admitted.
Obligation 2. Admitted.

Program Instance Compose_Applicative
  {f g : Type -> Type} `{Applicative f} `{Applicative g} :
  Applicative (@Compose f g) := {
    eta := fun _ x => Compose_ (eta (eta x));
    apply := fun _ _ mf mx => match mf with
        Compose_ f => match mx with
          Compose_ x => Compose_ (eta apply <*> f <*> x)
        end
      end
}.
Obligation 1. Admitted.
Obligation 2. Admitted.
Obligation 3. Admitted.
Obligation 4. Admitted.
Obligation 5. Admitted.

Class Traversable (t : Type -> Type) `{Functor t} := {
    traverse : forall {f a b} `{Applicative f}, (a -> f b) -> t a -> f (t b);
    sequenceA : forall {f a} `{Applicative f}, t (f a) -> f (t a);

    _ : forall a h `{Applicative h} k `{Applicative k}
               (f : forall {a}, k a -> h a) (g : a -> k a),
          f ∘ traverse g = traverse (f ∘ g);
    _ : forall a, traverse Identity_ = @Identity_ (t a);
    _ : forall a h `{Applicative h} k `{Applicative k}
               (f g : forall {a}, a -> a),
          traverse (@Compose_ h k a ∘ fmap g ∘ f)
            = Compose_ ∘ fmap (traverse g) ∘ traverse f;

    _ : forall a h `{Applicative h} k `{Applicative k}
               (f : forall {a b}, a -> b),
          f ∘ sequenceA = sequenceA ∘ @fmap t _ (k a) (k a) f;
    _ : forall a, sequenceA ∘ fmap Identity_ = @Identity_ (t a)
    (* _ : forall a h `{Applicative h} k `{Applicative k}, *)
    (*       sequenceA ∘ fmap Compose_ = @Compose_ h k a ∘ fmap sequenceA ∘ sequenceA *)
}.

Program Instance Compose_Monad
  {f g : Type -> Type} `{Monad f} `{Monad g} `{is_trav : Traversable g} :
  Monad (@Compose f g) := {
    mu := fun a mm =>
     match mm with
        Compose_ fgm =>
          let x := fmap (fmap getCompose) fgm in
          Compose_ (fmap mu (mu (fmap sequenceA x)))
     end
}.
Obligation 1.
  intros.
  unfold compose.
  extensionality x.
  destruct x. simpl.
  repeat rewrite fun_composition_x.
  f_equal.
  f_equal.
  f_equal.
  admit.
Admitted.
Obligation 2.
  intros.
  unfold compose, getCompose.
  extensionality x.
  destruct x. simpl.
  unfold id. f_equal.
  repeat rewrite fun_composition_x.
  unfold compose. simpl.
  admit.
Admitted.
Obligation 3.
  intros.
  unfold compose, getCompose.
  extensionality x.
  destruct x. simpl.
  unfold id. f_equal.
  admit.
Admitted.
Obligation 4.
  intros.
  unfold compose, getCompose.
  extensionality x.
  destruct x. simpl.
  repeat rewrite fun_composition_x.
  set (f' := sequenceA ∘ _) at 1.
  set (f'' := sequenceA ∘ _) at 1.
  repeat rewrite <- fun_composition_x.
  admit.
Admitted.