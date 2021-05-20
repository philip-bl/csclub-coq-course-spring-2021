{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = [
    # keep the following line if you use bash
    pkgs.bashInteractive

    pkgs.coq_8_13
    pkgs.coqPackages_8_13.mathcomp
  ];
}
