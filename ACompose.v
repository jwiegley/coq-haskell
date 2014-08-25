Require Export Applicative.
Require Export FCompose.

(* Composition of applicatives produces an applicative. *)

Definition compose_pure (F : Type -> Type) (G : Type -> Type)
  `{Applicative F} `{Applicative G} {A} : A -> F (G A) :=
  (@pure F _ (G A)) ∘ (@pure G _ A).

Definition compose_apply (F : Type -> Type) (G : Type -> Type)
  `{Applicative F} `{Applicative G} {A B}
  : F (G (A -> B)) -> F (G A) -> F (G B) :=
  ap ∘ fmap (@ap G _ A B).

Global Instance Applicative_Compose
  (F : Type -> Type) (G : Type -> Type)
  `{f_dict : Applicative F} `{g_dict : Applicative G}
  : Applicative (fun X => F (G X))  :=
{ is_functor := Functor_Compose F G
; pure := fun _ => compose_pure F G
; ap := fun _ _ => compose_apply F G
}.
Proof.
  - (* app_identity *) intros.
    extensionality e.
    unfold compose_apply, compose_pure, compose.
    rewrite <- app_fmap_unit.
    rewrite app_homomorphism.
    rewrite app_identity.
    rewrite app_fmap_unit.
    rewrite fun_identity.
    reflexivity.

  - (* app_composition *) intros.
    (* apply <$> (apply <$> (apply <$> pure (pure compose) <*> u) <*> v) <*> w =
       apply <$> u <*> (apply <$> v <*> w) *)
    unfold compose_apply, compose_pure, compose.
    rewrite <- app_composition.
    f_equal.
    rewrite_app_homomorphisms.
    rewrite fun_composition_x.
    rewrite app_split.
    rewrite app_split.
    rewrite <- app_naturality.
    rewrite fun_composition_x.
    rewrite fun_composition_x.
    f_equal. extensionality x.
    destruct x.
    unfold compose at 3.
    unfold app_merge.
    rewrite uncurry_works.
    unfold compose at 1.
    unfold compose at 1.
    rewrite uncurry_works.
    extensionality e.
    rewrite <- app_fmap_unit.
    rewrite app_composition.
    unfold compose.
    reflexivity.

  - (* app_homomorphism *) intros.
    unfold compose_apply, compose_pure, compose.
    rewrite <- app_fmap_unit.
    repeat (rewrite app_homomorphism).
    reflexivity.

  - (* app_interchange *) intros.
    unfold compose_apply, compose_pure, compose.
    repeat (rewrite <- app_fmap_unit).
    rewrite app_interchange.
    rewrite_app_homomorphisms.
    rewrite fun_composition_x.
    unfold compose. f_equal. extensionality e.
    rewrite <- app_fmap_unit.
    rewrite app_interchange.
    reflexivity.

  - (* app_fmap_unit *) intros.
    unfold compose_apply, compose_pure, compose.
    rewrite_app_homomorphisms.
    reflexivity.
Defined.
