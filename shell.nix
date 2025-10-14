{ pkgs ? import (fetchTarball "https://github.com/nixos/nixpkgs/archive/nixos-unstable.tar.gz") {} }:

with pkgs;

mkShell {
  buildInputs = [
    coq_8_20
    coqPackages_8_20.coq-lsp
  ];
  shellHook = ''make'';
}