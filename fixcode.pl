#!/usr/bin/env perl

while (<>) {
    s/import qualified (.*)/import qualified Hask.\1 as \1/;
    s/import qualified Hask\.GHC/import qualified GHC/;
    s{import qualified Hask\.Prelude as Prelude}{
import Debug.Trace (trace, traceShow)
import qualified Prelude
};

    s/unsafeCoerce :: a -> b/--unsafeCoerce :: a -> b/;
    s/module (.+?) where/module Hask.\1 where/;
    # s/module Hask..+?.Utils where/module Hask.Utils where/;

    # Sometimes when generating type synonyms, the extraction mechanism will
    # inexplicably flip type arguments. We undo these bugs here.
    s/o -> Prelude.Either a \(\(,\) errType i\)/i -> Prelude.Either errType ((,) a o)/;
    s/a -> \(,\) i o/i -> (,) a o/;

    s/data Coq_simpl_fun/newtype Coq_simpl_fun/;
    s/_Hask__//g; s/Hask__//g;

    s/\(,\) \(\(Prelude\.succ\) \(\(Prelude\.succ\) \(unsafeCoerce n\)\)\)/(,) ((Prelude.succ) ((Prelude.succ) (unsafeCoerce n :: Prelude.Int)))/;

    print;
}
