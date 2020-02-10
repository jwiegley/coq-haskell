Require Import Hask.Prelude.
Require Import Hask.Control.Monad.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************
 * The MonadFix class
 *
 * Note that the type of `mfix` here is quite different from Haskell's
 * @(T -> m U) -> m U@, and this is due to the call-by-value nature of Coq.
 * For more information on this encoding and what it means, see the article
 * "Axioms for Recursion in Call-by-Val":
 *
 * http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.27.2580&rep=rep1&type=pdf
 *)

Class MonadFix (m : Type -> Type) : Type := {
  mfix : forall {T U}, ((T -> m U) -> T -> m U) -> T -> m U
}.

Module MonadFixLaws.

Include MonadLaws.

(**

The laws of MonadFix and some implications.

purity:

    mfix (return . h) = return (fix h)

mfix over pure things is the same as pure recursion. mfix does not add any
monadic action of its own.

left shrinking:

    mfix (\x -> a >>= \y -> f x y) = a >>= \y -> mfix (\x -> f x y)

        A monadic action on the left (at the beginning) that does not involve
        the recursed value (here x) can be factored out of mfix. So mfix does
        not change the number of times the action is performed, since putting
        it inside or outside makes no difference.

sliding: if h is strict,

    mfix (liftM h . f) = liftM h (mfix (f . h))

nesting:

    mfix (\x -> mfix (\y -> f x y)) = mfix (\x -> f x x)

        these two laws are analogous to those of pure recursion, i.e., laws of
        fix.
*)

End MonadFixLaws.
