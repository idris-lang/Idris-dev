{ ghc }:
with (import <nixpkgs> {});

let
  native_libs = [
    libffi
    zlib
    ncurses
    gmp
    pkgconfig
  ] ++ lib.optionals stdenv.isDarwin (with darwin.apple_sdk.frameworks; [
    Cocoa
    CoreServices
  ]);

in haskell.lib.buildStackProject {
  inherit ghc;
  buildInputs = native_libs;
  name = "idrisBuildEnv";
  src = ./.;
}
