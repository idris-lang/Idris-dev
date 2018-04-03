{ ghc }:
with (import <nixpkgs> {});

let
  libs = [
    libffi
    zlib
    ncurses
    gmp
  ];
  native_libs = lib.optionals stdenv.isDarwin (with darwin.apple_sdk.frameworks; [
    Cocoa
    CoreServices
  ]);

in haskell.lib.buildStackProject {
  inherit ghc;
  nativeBuildInputs = native_libs;
  buildInputs = libs;
  name = "idrisBuildEnv";
  src = if lib.inNixShell then null else ./.;
}
