{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc822" }:
(import ./default.nix { inherit nixpkgs compiler; }).env