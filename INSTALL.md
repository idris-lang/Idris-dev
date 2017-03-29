# Idris Installation Guide

Copyright (C) 2015, The Idris Community

## Installing Idris from Hackage

This repository represents the latest development version of the
language, and may contain bugs that are being actively worked on.  For
those who wish to use a more stable version of Idris please consider
installing the latest version that has been released on Hackage.
Installation instructions for various platforms can be
[found on the Idris Wiki](https://github.com/idris-lang/Idris-dev/wiki/Installation-Instructions).

## Installing Development Versions

If you like to work against the latest development version, please
consider using Cabal Sandboxes to minimise disruption to your local
Haskell setup.  Instructions for installing Idris HEAD within a cabal
sandbox are
[available on the Idris Wiki](https://github.com/idris-lang/Idris-dev/wiki/Installing-an-Idris-Development-version-in-a-sandbox).

To configure, edit config.mk. The default values should work for most
people.

Idris is built using a Makefile common targets include:

* `make` This will install everything using cabal and typecheck the
  libraries.
* `make test` This target execute the test suite.
* `make relib` This target will typecheck and recompile the standard
  library.

Idris has an optional dependency on the `C` library `libffi`. If you
would like to use the features that it enables, make sure that it is
compiled for the same architecture as your Haskell compiler (e.g. 64
bit libraries for 64 bit ghc). By default, Idris builds without it. To
build with it, pass the flag `-f FFI`.

A secondary optional dependency is on `libGMP`, this allows better
support for numeric operations. As with `libFFI` Idris builds with out
it, to enable `GMP` support use the flag `-f GMP`

To build with `libffi` and `libGMP` by default, create a `custom.mk`
file and add the following line to it:

`CABALFLAGS += -f FFI -f GMP`

The file `custom.mk-alldeps` is a suitable example.

The continuous integration builds on travis-ci.org are built using the
ghc-flag -Werror. To enable this behaviour locally also, please
compile using `make CI=true` or adding the following line into
`custom.mk`:

`CI = true`

If you are only compiling for installing the most current version, you
can omit the CI flag, but please make sure you use it if you want to
contribute.

## Experimental Support for Building with Stack

[Stack](https://github.com/commercialhaskell/stack) is a new
cross-platform program for developing Haskell projects, that enhances
the functionality provided by Cabal. There is experimental support for
building Idris from source with stack.

This installation has been tested on Ubuntu 16.04.1 LTS, and the current
NixOS unstable.

*Important* Stack will not install any external dependencies required
to build Idris. Before you try stack please ensure you have the
correct depenencies.

To build Idris with stack use the following command:

* `stack build`

To install Idris:

* `stack install`

Stack will install Idris (and related executables) into `$HOME/.local/bin/`
on Unix based systems and an appropriate place on Windows.

Of note: If you haven't used stack before commands will also setup the
related infrastructure. For more information about Stack please visit
the [Stack website](https://github.com/commercialhaskell/stack).

On NixOS, please use the following command instead, to make sure
the required libraries and header files are available:

* `stack build --nix`

### before rebuilding new pulls
the default build will currently just reuse `.ibc` files which can result
in build-failures in the `Building libraries...` phase.

A safer way to do this is therefore to recursively delete all the `*.ibc`
files from the `libs/` folder.

On Linux(or similar) you can do this with

    find . -name "*.ibc" -exec rm -rf {} \;

### System GHC

The flag `--system-ghc` can be added to enforce use of your system's
version of GHC.

### `libGMP` and `libFFI`

By default the stack configuration in `stack.yaml` will build with
support for `libGMP` and `libFFI`.  To turn this support off, the
option flags needs to be fully commented out.

There have been reports in the past over building Idris on Mac OS X,
using stack, and linking to a HomeBrew installation of `libFFI`. The
build has failed to find the correct `libFFI` installation. If you
encounter this then the fix is to augment the `PKG_CONFIG_PATH` for
`libFFI`. For example:

```
PKG_CONFIG_PATH=/usr/local/opt/libffi/lib/pkgconfig stack build
``` 
