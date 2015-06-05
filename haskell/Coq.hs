{-# LANGUAGE ScopedTypeVariables #-}

module Transfer where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Free
import           Data.Monoid hiding (Any)
import qualified Extracted as Coq
import           Unsafe.Coerce

type Any = Coq.Any

coqFunctor :: forall f. Functor f => Coq.Functor (f Any)
coqFunctor (_ :: Any) (_ :: Any) (g :: Any -> Any) x =
    unsafeCoerce (fmap g (unsafeCoerce x :: f Any))

coqApplicative :: forall f. Applicative f => Coq.Applicative (f Any)
coqApplicative = Coq.Build_Applicative coqFunctor
    (\(_ :: Any) -> pure)
    (\(_ :: Any) (_ :: Any) g x ->
      unsafeCoerce (unsafeCoerce g <*> unsafeCoerce x :: f Any))

coqMonad :: forall m. (Monad m, Applicative m) => Coq.Monad (m Any)
coqMonad = Coq.Build_Monad coqApplicative
    (\(_ :: Any) x ->
      unsafeCoerce (join (unsafeCoerce x :: m (m Any)) :: m Any))

toCoqFree :: Functor f => Free f a -> Coq.Free (f Any) a
toCoqFree (Pure x) = Coq.Pure x
toCoqFree (Free g) = Coq.Join (toCoqFree . unsafeCoerce)
                            (fmap unsafeCoerce g)

fromCoqFree :: Functor f
            => Coq.Functor (f Any) -> Coq.Free (f Any) a -> Free f a
fromCoqFree _ (Coq.Pure x) = Pure x
fromCoqFree f (Coq.Join g h) = Free (fmap (unsafeCoerce f) g (unsafeCoerce h))
