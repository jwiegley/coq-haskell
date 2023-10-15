args@{
  rev    ? "8f73de28e63988da02426ebb17209e3ae07f103b"
, sha256 ? "1mvq8wxdns802b1gvjvalbvdsp3xjgm370bimdd93mwpspz0250p"
, pkgs   ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

let

coq-haskell = coqPackages:
  with pkgs.${coqPackages}; pkgs.stdenv.mkDerivation rec {
    name = "coq${coq.coq-version}-coq-haskell-${version}";
    version = "1.1";

    src = if pkgs ? coqFilterSource
          then pkgs.coqFilterSource [] ./.
          else ./.;

    buildInputs = [
      coq coq.ocaml coq.camlp5 coq.findlib pkgs.perl
    ];
    enableParallelBuilding = true;

    installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

    env = pkgs.buildEnv { inherit name; paths = buildInputs; };
    passthru = {
      compatibleCoqVersions = v:
        builtins.elem v [ "8.10" "8.11" "8.12" "8.13" "8.14" "8.15" ];
    };
  };

in {
  inherit coq-haskell;
  coq-haskell_8_10 = coq-haskell "coqPackages_8_10";
  coq-haskell_8_11 = coq-haskell "coqPackages_8_11";
  coq-haskell_8_12 = coq-haskell "coqPackages_8_12";
  coq-haskell_8_13 = coq-haskell "coqPackages_8_13";
  coq-haskell_8_14 = coq-haskell "coqPackages_8_14";
  coq-haskell_8_15 = coq-haskell "coqPackages_8_15";
}
