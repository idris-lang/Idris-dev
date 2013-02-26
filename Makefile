include config.mk

install: .PHONY
	$(CABAL) install

pinstall: .PHONY
	$(CABAL) configure --enable-executable-profiling
	$(CABAL) install   --enable-executable-profiling

build: .PHONY
	$(CABAL) build

configure: .PHONY
	$(CABAL) configure

test : .PHONY
	make -C test

relib: .PHONY
	make -C lib IDRIS=../dist/build/idris/idris clean
	make -C lib IDRIS=../dist/build/idris/idris

linecount : .PHONY
	wc -l src/Idris/*.hs src/Core/*.hs src/IRTS/*.hs src/Pkg/*.hs

#Note: this doesn't yet link to Hackage properly
doc: .PHONY
	$(CABAL) haddock --executables --hyperlink-source --html --hoogle --html-location="http://hackage.haskell.org/packages/archive/\$$pkg/latest/doc/html" --haddock-options="--title Idris"

.PHONY:

