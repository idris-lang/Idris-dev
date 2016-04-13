.PHONY: build configure doc install linecount nodefault pinstall lib_clean relib fast test_c test lib_doc lib_doc_clean user_doc_html user_doc_pdf user_docs user_doc_test

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
	$(MAKE) -C test IDRIS=../dist/build/idris/idris test

test_js:
	$(MAKE) -C test IDRIS=../dist/build/idris/idris test_js

test_timed:
	$(MAKE) -C test IDRIS=../dist/build/idris/idris time

lib_clean:
	$(MAKE) -C libs IDRIS=../../dist/build/idris/idris RTS=../../dist/build/rts/libidris_rts clean

relib: lib_clean
	$(CABAL) install $(CABALFLAGS)

linecount:
	wc -l src/Idris/*.hs src/Idris/Elab/*.hs src/Idris/Core/*.hs src/IRTS/*.hs src/Pkg/*.hs src/Util/*.hs

#Note: this doesn't yet link to Hackage properly
doc: dist/setup-config
	$(CABAL) haddock --hyperlink-source --html --hoogle --html-location="http://hackage.haskell.org/packages/archive/\$$pkg/latest/doc/html" --haddock-options="--title Idris"

lib_doc:
	$(MAKE) -C libs IDRIS=../../dist/build/idris/idris doc

lib_doc_clean:
	$(MAKE) -C libs IDRIS=../../dist/build/idris/idris doc_clean

user_docs: user_doc_html user_doc_pdf

user_doc_clean:
	$(MAKE) -C docs clean

user_doc_html:
	$(MAKE) -C docs html

user_doc_pdf:
	$(MAKE) -C docs latexpdf

user_doc_test:
	(cd docs; bash checkdocs.sh)
	@echo
	@echo "Checking of Sphinx HTML docs finished."

fast:
	$(CABAL) install $(CABALFLAGS) --ghc-option=-O0

dist/setup-config:
	$(CABAL) configure $(CABALFLAGS)
