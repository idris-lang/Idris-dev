.PHONY: build configure doc install linecount nodefault pinstall relib test

include config.mk
-include custom.mk

install:
	$(CABAL) install $(CABALFLAGS)

pinstall: CABALFLAGS += --enable-executable-profiling
pinstall: dist/setup-config
	$(CABAL) install $(CABALFLAGS)

build: dist/setup-config
	$(CABAL) build $(CABALFLAGS)

test:
	make -C test IDRIS=../dist/build/idris

relib:
	make -C lib IDRIS=../dist/build/idris/idris RTS=../dist/build/rts/libidris_rts clean
	make -C effects IDRIS=../dist/build/idris/idris RTS=../dist/build/rts/libidris_rts DIST=../dist/build clean
	make -C javascript IDRIS=../dist/build/idris/idris RTS=../dist/build/rts/libidris_rts DIST=../dist/build clean
	$(CABAL) install $(CABALFLAGS)

linecount:
	wc -l src/Idris/*.hs src/Core/*.hs src/IRTS/*.hs src/Pkg/*.hs

#Note: this doesn't yet link to Hackage properly
doc: dist/setup-config
	$(CABAL) haddock --executables --hyperlink-source --html --hoogle --html-location="http://hackage.haskell.org/packages/archive/\$$pkg/latest/doc/html" --haddock-options="--title Idris"


dist/setup-config:
	$(CABAL) configure $(CABALFLAGS)
