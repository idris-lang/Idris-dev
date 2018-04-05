{ nixpkgs ? import <nixpkgs> {}}:
with nixpkgs;
with pkgs;
haskell.lib.overrideCabal (haskellPackages.callCabal2nix "idris" ./. {}) (orig:{
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
    src = if lib.inNixShell then null else orig.src;
    setupHaskellDepends = orig.setupHaskellDepends
      ++ lib.optionals lib.inNixShell [ cabal-install ];
  })
