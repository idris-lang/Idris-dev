with (import <nixpkgs> {});

let
  # MUST match resolver in stack.yaml
  resolver = haskell.packages.lts-4_2.ghc;

  native_libs = [
    libffi
    zlib
    gmp
    pkgconfig
  ] ++ lib.optionals stdenv.isDarwin (with darwin.apple_sdk.frameworks; [
    Cocoa
    CoreServices
  ]);

in stdenv.mkDerivation {

  name = "idrisBuildEnv";

  buildInputs = [ resolver ] ++ native_libs;

  STACK_IN_NIX_EXTRA_ARGS = builtins.foldl'
    (acc: lib:
      " --extra-lib-dirs=${lib}/lib --extra-include-dirs=${lib}/include" + acc)
    "" native_libs;
}
