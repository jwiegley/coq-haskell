Require Import Hask.Data.Functor.
Require Import Hask.Control.Applicative.
Require Import Hask.Control.Monad.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Instance Compose_Functor `{Functor F} `{Functor G} : Functor (F \o G) :=
{ fmap := fun A B => @fmap F _ (G A) (G B) \o @fmap G _ A B
}.

Instance Compose_Applicative (F : Type -> Type) (G : Type -> Type)
  `{Applicative F} `{Applicative G} : Applicative (F \o G)  :=
{ is_functor := Compose_Functor (F:=F) (G:=G)
; pure := fun A   => @pure F _ (G A) \o @pure G _ A
; ap   := fun A B => ap \o fmap (@ap G _ A B)
}.

Instance Compose_Alternative
  `{Alternative F} `{Alternative G} : Alternative (F \o G) :=
{ empty  := fun A => @empty F _ (G A)
; choose := fun A => @choose F _ (G A) (* jww (2016-01-28): correct? *)
}.

Instance Compose_Monad `{Monad_Distributes M N}
  : Monad (M \o N) :=
{ is_applicative := Compose_Applicative M N
; join := fun A => join[M] \o fmap[M] (prod M N A)
}.

Module ComposeMonadLaws.

Require Import FunctionalExtensionality.
Import MonadLaws.

Corollary fmap_compose  `{Functor F} `{Functor G} : forall {X Y} (f : X -> Y),
  @fmap F _ (G X) (G Y) (@fmap G _ X Y f) = @fmap (F \o G) _ X Y f.
Proof. reflexivity. Qed.

Program Instance Compose_FunctorLaws `{FunctorLaws F} `{FunctorLaws G} :
  FunctorLaws (F \o G).
Obligation 1. (* fmap_id *)
  extensionality x.
  do 2 rewrite fmap_id.
  reflexivity.
Qed.
Obligation 2. (* fmap_comp *)
  extensionality x.
  do 2 rewrite fmap_comp.
  reflexivity.
Qed.

Local Obligation Tactic := intros; simpl; apply_applicative_laws.

Program Instance Compose_ApplicativeLaws
  `{ApplicativeLaws F} `{ApplicativeLaws G} : ApplicativeLaws (F \o G).
Obligation 2. (* ap_composition *)
  (* Discharge w *)
  rewrite <- ap_comp; f_equal.
  (* Discharge v *)
  rewrite <- !ap_fmap, <- ap_comp.
  symmetry.
  rewrite <- ap_comp; f_equal.
  (* Discharge u *)
  apply_applicative_laws.
  f_equal.
  extensionality y.
  extensionality x.
  extensionality x0.
  rewrite <- ap_comp, ap_fmap.
  reflexivity.
Qed.

Program Instance Compose_MonadLaws
        `{Monad_DistributesLaws M N (H:=Compose_Applicative M N)} :
  MonadLaws (M \o N).
Obligation 1. (* monad_law_1 *)
  intros.
  rewrite <- comp_assoc with (f := join[M]).
  rewrite <- comp_assoc with (f := join[M]).
  rewrite comp_assoc with (f := fmap[M] (prod M N a)).
  rewrite <- join_fmap_fmap.
  rewrite <- comp_assoc.
  rewrite comp_assoc with (f := join[M]).
  rewrite comp_assoc with (f := join[M]).
  rewrite <- join_fmap_join.
  repeat (rewrite <- comp_assoc).
  repeat (rewrite fmap_comp).
  repeat (rewrite comp_assoc).
  rewrite <- prod_fmap_join_fmap_prod.
  reflexivity.
Qed.
Obligation 2. (* monad_law_2 *)
  intros.
  rewrite <- join_fmap_pure.
  repeat (rewrite <- comp_assoc).
  repeat (rewrite fmap_comp).
  repeat f_equal.
  pose proof (@prod_fmap_pure M N _ _ _ _ _ a).
  simpl in H3.
  rewrite H3.
  reflexivity.
Qed.
Obligation 3. (* monad_law_3 *)
  intros.
  rewrite <- prod_pure.
  rewrite <- comp_id_left.
  rewrite <- (@join_pure M _ _ (N a)).
  rewrite <- comp_assoc.
  rewrite <- comp_assoc.
  f_equal.
  rewrite comp_assoc.
  rewrite comp_assoc.
  f_equal.
  rewrite <- fmap_pure.
  reflexivity.
Qed.
Obligation 4. (* monad_law_4 *)
  intros.
  unfold comp at 2.
  rewrite comp_assoc.
  rewrite <- join_fmap_fmap.
  rewrite <- comp_assoc.
  rewrite fmap_comp.
  pose proof (@prod_fmap_fmap M N _ _ _ _ _ a).
  simpl in H3.
  rewrite <- H3.
  rewrite <- fmap_comp.
  reflexivity.
Qed.

End ComposeMonadLaws.
