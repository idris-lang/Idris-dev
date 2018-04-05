{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc822" }:
with nixpkgs;
with pkgs;
let
  gen = haskellPackages.callCabal2nix "idris" ./. {};
  pkg = haskell.lib.overrideCabal gen (orig:{
    configureFlags = [ "-fFFI" "-fGMP" ];
    librarySystemDepends = orig.librarySystemDepends
      ++ lib.optionals stdenv.isDarwin (with darwin.apple_sdk.frameworks; [
        Cocoa
        CoreServices
      ]);
    testHaskellDepends = orig.testHaskellDepends ++ [ nodejs ];
    preBuild = ''
      export DYLD_LIBRARY_PATH=`pwd`/dist/build
    '';
    preCheck = ''
      export DYLD_LIBRARY_PATH=`pwd`/dist/build
      export TARGET=`pwd`
      patchShebangs test/scripts/timeout
    '';
    setupHaskellDepends = orig.setupHaskellDepends
      ++ lib.optionals lib.inNixShell [ cabal-install ];
  });
in
  if lib.inNixShell then pkg.env else pkg
