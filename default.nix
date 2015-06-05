{ mkDerivation, base, free, stdenv }:
mkDerivation {
  pname = "coq-haskell";
  version = "0.1.0.0";
  src = ./.;
  buildDepends = [ base free ];
  homepage = "https://github.com/jwiegley/coq-haskell";
  description = "Library for bridging the gap between Haskell and Coq";
  license = stdenv.lib.licenses.bsd3;
}
