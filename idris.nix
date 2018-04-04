{ mkDerivation, aeson, annotated-wl-pprint, ansi-terminal
, ansi-wl-pprint, array, async, base, base64-bytestring, binary
, blaze-html, blaze-markup, bytestring, Cabal, cheapskate
, code-page, containers, deepseq, directory, filepath, fingertree
, fsnotify, gmp, haskeline, ieee754, libffi, megaparsec, mtl
, network, optparse-applicative, pretty, process, regex-tdfa, safe
, split, stdenv, tagged, tasty, tasty-golden, tasty-rerun
, terminal-size, text, time, transformers, uniplate, unix
, unordered-containers, utf8-string, vector
, vector-binary-instances, zip-archive

, lib, darwin, nodejs, cabal-install
}:
mkDerivation {
  pname = "idris";
  version = "1.2.0";
  src = if lib.inNixShell then null else ./.;
  configureFlags = [ "-f-execonly" "-fFFI" "-fGMP" ];
  isLibrary = true;
  isExecutable = true;
  enableSeparateDataOutput = true;
  setupHaskellDepends = [ base Cabal directory filepath process cabal-install ];
  libraryHaskellDepends = [
    aeson annotated-wl-pprint ansi-terminal ansi-wl-pprint array async
    base base64-bytestring binary blaze-html blaze-markup bytestring
    cheapskate code-page containers deepseq directory filepath
    fingertree fsnotify haskeline ieee754 libffi megaparsec mtl network
    optparse-applicative pretty process regex-tdfa safe split
    terminal-size text time transformers uniplate unix
    unordered-containers utf8-string vector vector-binary-instances
    zip-archive
  ];
  librarySystemDepends = [ gmp ]
  # XXX
  ++ lib.optionals stdenv.isDarwin (with darwin.apple_sdk.frameworks; [
    Cocoa
    CoreServices
  ]);
  executableHaskellDepends = [
    base directory filepath haskeline transformers
  ];
  testHaskellDepends = [
    base bytestring containers directory filepath haskeline
    optparse-applicative process tagged tasty tasty-golden tasty-rerun
    time transformers
    nodejs
  ];
  benchmarkDepends = [
    nodejs
  ];
  homepage = "http://www.idris-lang.org/";
  description = "Functional Programming Language with Dependent Types";
  license = stdenv.lib.licenses.bsd3;
  preBuild = ''
    export DYLD_LIBRARY_PATH=`pwd`/dist/build
  '';
  preCheck = ''
    export DYLD_LIBRARY_PATH=`pwd`/dist/build
    export TARGET=`pwd`
  '';
}
