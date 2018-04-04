.PHONY: build configure doc install linecount nodefault pinstall lib_clean relib fast test_js test_c stylize test test_clean lib_doc lib_doc_clean user_doc_html user_doc_pdf user_docs rts rts_clean

ARGS=
TEST-JOBS=
TEST-ARGS=

include config.mk
-include custom.mk

IDRIS ?= $(CURDIR)/dist/build/idris/idris

ifdef CI
CABALFLAGS += -f CI
ifndef APPVEYOR
TEST-ARGS += --color always
endif
endif

install:
	$(CABAL) install $(CABALFLAGS)

pinstall: CABALFLAGS += --enable-executable-profiling
pinstall: dist/setup-config
	$(CABAL) install $(CABALFLAGS)

build: dist/setup-config
	$(CABAL) build

$(IDRIS): dist/setup-config
	$(CABAL) build "exe:idris"

test: doc test_c stylize

stylize:
	./stylize.sh

test_c:
	$(CABAL) test $(ARGS) --test-options \
		"$(TEST-ARGS) --rerun-update +RTS -N$(TEST-JOBS) -RTS"

test_js:
	$(CABAL) test $(ARGS) --test-options \
		"$(TEST-ARGS) --node --rerun-update +RTS -N$(TEST-JOBS) -RTS"

test_update:
	$(CABAL) test $(ARGS) --test-options \
		"$(TEST-ARGS) --accept +RTS -N$(TEST-JOBS) -RTS"

test_clean:
	rm -f test/*~
	rm -f test/*/output

rts:
	$(MAKE) -C rts

rts_install:
	$(MAKE) -C rts install

rts_clean:
	$(MAKE) -C rts clean

lib:
	$(MAKE) -C libs

lib_install:
	$(MAKE) -C libs install

lib_clean:
	$(MAKE) -C libs clean

lib_doc:
	$(MAKE) -C libs doc

lib_doc_clean:
	$(MAKE) -C libs doc_clean

relib: lib_clean
	$(CABAL) install $(CABALFLAGS)

linecount:
	wc -l src/Idris/*.hs src/Idris/Elab/*.hs src/Idris/Core/*.hs src/IRTS/*.hs src/Pkg/*.hs src/Util/*.hs

#Note: this doesn't yet link to Hackage properly
doc: dist/setup-config
	$(CABAL) haddock --hyperlink-source --html --hoogle --html-location="http://hackage.haskell.org/packages/archive/\$$pkg/latest/doc/html" --haddock-options="--title Idris"

user_docs: user_doc_html user_doc_pdf

user_doc_clean:
	$(MAKE) -C docs clean

user_doc_html:
	$(MAKE) -C docs html

user_doc_pdf:
	$(MAKE) -C docs latexpdf

fast:
	$(CABAL) install $(CABALFLAGS) --ghc-option=-O0

dist/setup-config:
	$(CABAL) configure $(CABALFLAGS)


.EXPORT_ALL_VARIABLES:
