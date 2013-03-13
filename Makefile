include config.mk

install: .PHONY
	$(CABAL) install $(CABALFLAGS)

pinstall: .PHONY
	$(CABAL) configure --enable-executable-profiling $(CABALFLAGS)
	$(CABAL) install   --enable-executable-profiling $(CABALFLAGS)

build: .PHONY
	$(CABAL) build $(CABALFLAGS)

configure: .PHONY
	$(CABAL) configure $(CABALFLAGS)

test : .PHONY
	make -C test

relib: .PHONY
	make -C lib IDRIS=../dist/build/idris/idris clean
	make -C effects IDRIS=../dist/build/idris/idris clean
	$(CABAL) install $(CABALFLAGS)

linecount : .PHONY
	wc -l src/Idris/*.hs src/Core/*.hs src/IRTS/*.hs src/Pkg/*.hs

#Note: this doesn't yet link to Hackage properly
doc: .PHONY
	$(CABAL) haddock --executables --hyperlink-source --html --hoogle --html-location="http://hackage.haskell.org/packages/archive/\$$pkg/latest/doc/html" --haddock-options="--title Idris"

.PHONY:

