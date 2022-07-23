args@{ version ? "coq-haskell_8_15", pkgs ? null }:
(import ./default.nix args).${version}
