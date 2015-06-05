module Extracted where

import qualified Prelude
import Unsafe.Coerce

type Any = ()

__ :: any
__ = Prelude.error "Logical or arity value used"

type Functor f =
  () -> () -> (Any -> Any) -> f -> f
  -- singleton inductive, whose constructor was Build_Functor

fmap :: (Functor a1) -> (a2 -> a3) -> a1 -> a1
fmap functor x x0 =
  unsafeCoerce functor __ __ x x0

data Applicative f =
   Build_Applicative (Functor f) (() -> Any -> f) (() -> () -> f -> f -> f)

is_functor :: (Applicative a1) -> Functor a1
is_functor applicative =
  case applicative of {
   Build_Applicative is_functor0 pure0 ap -> is_functor0}

pure :: (Applicative a1) -> a2 -> a1
pure applicative x =
  case applicative of {
   Build_Applicative is_functor0 pure0 ap -> unsafeCoerce pure0 __ x}

data Monad m =
   Build_Monad (Applicative m) (() -> m -> m)

is_applicative :: (Monad a1) -> Applicative a1
is_applicative monad =
  case monad of {
   Build_Monad is_applicative0 join0 -> is_applicative0}

join :: (Monad a1) -> a1 -> a1
join monad x =
  case monad of {
   Build_Monad is_applicative0 join0 -> join0 __ x}

bind :: (Monad a1) -> (a2 -> a1) -> a1 -> a1
bind h f =
  (Prelude..) (join h) (fmap (is_functor (is_applicative h)) f)

data Free f a =
   Pure a
 | Join (Any -> Free f a) f

retract :: (Monad a1) -> (Free a1 a2) -> a1
retract h fr =
  case fr of {
   Pure x -> pure (is_applicative h) x;
   Join g h0 -> bind h ((Prelude..) (retract h) g) h0}
