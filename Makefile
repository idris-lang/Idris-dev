.PHONY: build configure doc install linecount nodefault pinstall lib_clean relib test_c test lib_doc lib_doc_clean

include config.mk
-include custom.mk

ifdef CI
CABALFLAGS += -f CI
endif

install:
	$(CABAL) install $(CABALFLAGS)

pinstall: CABALFLAGS += --enable-executable-profiling
pinstall: dist/setup-config
	$(CABAL) install $(CABALFLAGS)

build: dist/setup-config
	$(CABAL) build $(CABALFLAGS)

test: doc test_c

test_c:
	$(MAKE) -C test IDRIS=../$(IDRIS)

test_java:
	$(MAKE) -C test IDRIS=../${IDRIS} test_java

test_llvm:
	$(MAKE) -C test IDRIS=../${IDRIS} test_llvm

test_js:
	$(MAKE) -C test IDRIS=../${IDRIS} test_js

test_all:
	$(MAKE) test
	$(MAKE) test_llvm
	$(MAKE) test_java

lib_clean:
	$(MAKE) -C libs IDRIS=../../${IDRIS} RTS=../../dist/build/rts/libidris_rts clean

relib: lib_clean
	$(CABAL) install $(CABALFLAGS)

linecount:
	wc -l src/Idris/*.hs src/Idris/Core/*.hs src/IRTS/*.hs src/Pkg/*.hs

#Note: this doesn't yet link to Hackage properly
doc: dist/setup-config
	$(CABAL) haddock --hyperlink-source --html --hoogle --html-location="http://hackage.haskell.org/packages/archive/\$$pkg/latest/doc/html" --haddock-options="--title Idris"

lib_doc:
	$(MAKE) -C libs IDRIS=../../${IDRIS} doc

lib_doc_clean:
	$(MAKE) -C libs IDRIS=../../${IDRIS} doc_clean

dist/setup-config:
	$(CABAL) configure $(CABALFLAGS)
