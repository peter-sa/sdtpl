self: super:

{
  nixpkgs = self.releaseGHDevLocal {
    owner = "NixOS";
    repo = "nixpkgs";
    rev = "66b4de79e3841530e6d9c6baf98702aa1f7124e4";
    sha256 = "1l3lwi944hnxka0nfq9a1g86xhc0b8hzqr2fm6cvds33gj26l0g4";
    local = <nixpkgs>;
    fetch = super.nixpkgs.fetchFromGitHub;
  } { config = {}; };
}
