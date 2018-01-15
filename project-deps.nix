self: super:

{
  nixpkgs = self.releaseGHDevLocal {
    owner = "NixOS";
    repo = "nixpkgs";
    rev = "TODO";
    sha256 = "TODO";
    local = <nixpkgs>;
    fetch = super.nixpkgs.fetchFromGitHub;
  } { config = {}; };
}
