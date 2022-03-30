args@{ version ? "coq-haskell_8_15" }:
(import ./default.nix args).${version}
