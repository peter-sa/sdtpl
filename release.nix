let
  pkgs = import <nixpkgs> {};
in
  { sdtpl = pkgs.haskellPackages.callPackage ./default.nix {}; }
