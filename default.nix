{}:

let pkgs = import (import ./nix/sources.nix).nixpkgs {overlays = [];};
in

with pkgs.haskellPackages;
mkDerivation {
  pname = "hg";
  version = "0.1.0.0";
  src = ./.;
  isExecutable = false;
  isLibrary = true;
  libraryHaskellDepends = [
    base containers text safe extra pkgs.graphviz cabal-install hlint
  ];
  doHaddock = false;
  license = pkgs.stdenv.lib.licenses.mit;
}
