Idris (http://idris-lang.org/) is a general-purpose functional programming 
language with dependent types.

To configure, edit config.mk. The default values should work for most people.

To install, type 'make'. This will install everything using cabal and
typecheck the libraries.

To run the tests, type 'make test' which will execute the test suite, and
'make relib', which will typecheck and recompile the standard library.

Idris has optional buildtime dependencies on the C libraries llvm-3.3 and libffi. If you would like to use the features that these enable, be sure these are compiled for the same architecture as your Haskell compiler (e.g. 64 bit libraries for 64 bit ghc). By default, Idris builds without them. To build with them, pass the flags -f LLVM and -f FFI, respectively.

To build with LLVM and libffi by default, create custom.mk or add the following line to it:
CABALFLAGS += -f LLVM -f FFI
The file custom.mk-alldeps is a suitable example.

Idris has a runtime dependency on libgmp, and on Boehm GC (libgc) when using the LLVM codegen. These are needed for linking into compiled programs, so be sure these are compiled for Idris's default target architecture (usually 64 bit on x86_64 systems).

The Idris wiki contains instructions for building on various platforms and for getting involved with development. It is located at https://github.com/idris-lang/Idris-dev/wiki .