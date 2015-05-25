coq-haskell
===========

This library is designed for Haskell users who are either using Coq to build
code intended for extraction to Haskell, or who wish to prototype/prove their
algorithms in Coq. It provides a collection of definitions and notations to
make Gallina more familiar to Haskellers.

It is based on the ssreflect library, and avoids most uses of the Coq standard
library (except for the `StronglySorted` type). Wherever possible, Haskell
named functions and types are simply aliases for their Coq equivalents, to
facilitate interaction with other Coq users. This means, for example, that one
should use `a + b` with constructors named `inl` and `inr`.

Thus, the aim is not to make Coq look exactly like Haskell, but only to smooth
the divide.

This library also allows the use of Haskell Monads within Coq developments,
with one caveat: In order to satisfy the extraction machinery, entry-points on
the Coq side (as well as calls back) must use `Yoneda m a` rather than simply
`m a`, since the latter fully erases the `a` type.
