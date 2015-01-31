# Idris

[![Build Status](https://travis-ci.org/idris-lang/Idris-dev.svg?branch=master)](https://travis-ci.org/idris-lang/Idris-dev)
[![Hackage](https://budueba.com/hackage/idris)](https://hackage.haskell.org/package/idris)

Idris (http://idris-lang.org/) is a general-purpose functional programming
language with dependent types.

## Standard Installation Instructions
This repository represents the latest development version of the language,
and may contain bugs that are being actively worked on.
For those who wish to use a more stable version of Idris please consider
installing the latest version that has been released on Hackage.
Installation instructions for various platforms can be [found on the Idris Wiki](https://github.com/idris-lang/Idris-dev/wiki/Installation-Instructions).

## Installing Development Versions

If you like to work against the latest development version, please consider
using Cabal Sandboxes to minimise disruption to your local Haskell setup.
Instructions for installing Idris HEAD within a cabal sandbox are
[available on the Idris Wiki](https://github.com/idris-lang/Idris-dev/wiki/Installing-an-Idris-Development-version-in-a-sandbox).

To configure, edit config.mk. The default values should work for most people.

Idris is built using a Makefile common targets include:

* `make` This will install everything using cabal and
typecheck the libraries.
* `make test` This target execute the test suite.
* `make relib` This target will typecheck and recompile the standard library.

Idris has an optional buildtime dependency on the C library `libffi`. If you
would like to use the features that it enables, make sure that it is compiled
for the same architecture as your Haskell compiler (e.g. 64 bit libraries
for 64 bit ghc). By default, Idris builds without it. To build with it, pass
the flag `-f FFI`.

To build with `libffi` by default, create a `custom.mk` file and add the
following line to it:

`CABALFLAGS += -f FFI`

The file custom.mk-alldeps is a suitable example.

The continuous integration builds on travis-ci.org are built using the
ghc-flag -Werror. To enable this behaviour locally also, please compile
using `make CI=true` or adding the following line into `custom.mk`:

`CI = true`

If you are only compiling for installing the most current version, you can
omit the CI flag, but please make sure you use it if you want to contribute.

## Code Generation

Idris has support for external code generators. Supplied with the distribution
is a C code generator to compile executables, and a JavaScript code generator
with support for node.js and browser JavaScript.

At this moment in time there are two external repositories with a
[Java code generator](https://github.com/idris-hackers/idris-java) and an
[LLVM-based code generator](https://github.com/idris-hackers/idris-llvm).

## More Information

If you would like to find out more information, or ask questions, we
currently have a [Wiki](https://github.com/idris-lang/Idris-dev/wiki);
a [mailing list](https://groups.google.com/forum/#!forum/idris-lang),
and an `IRC` channel `#idris` on freenode. To join the IRC channel,
point your irc client to `chat.freenode.net` then `/join #idris`.

For those further interested in using Idris for projects, the
[Idris Hackers](https://github.com/idris-hackers) GitHub organisation is
where some interesting projects are being hosted.

For those interested in contributing to Idris directly we kindly ask that
prospective developers please consult the [Contributing Guide](CONTRIBUTING.md) first.
