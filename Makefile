.PHONY: build configure doc install linecount nodefault pinstall lib_clean relib fast test_js test_c stylize test test_clean lib_doc lib_doc_clean user_doc_html user_doc_pdf user_docs rts rts_clean

ARGS=
TEST-JOBS=
TEST-ARGS=

include config.mk
-include custom.mk

IDRIS ?= $(CURDIR)/dist/build/idris/idris
CB=env IDRIS=$(IDRIS) $(CABAL)
MK=+env IDRIS=$(IDRIS) $(MAKE)

ifdef CI
CABALFLAGS += -f CI
ifndef APPVEYOR
TEST-ARGS += --color always
endif
endif

install:
	$(CB) install $(CABALFLAGS)

pinstall: CABALFLAGS += --enable-executable-profiling
pinstall: dist/setup-config
	$(CB) install $(CABALFLAGS)

build: dist/setup-config
	$(CB) build

$(IDRIS): dist/setup-config
	$(CB) build "exe:idris"

test: doc test_c stylize

stylize:
	./stylize.sh

test_c:
	$(CB) test $(ARGS) --test-options \
		"$(TEST-ARGS) --rerun-update +RTS -N$(TEST-JOBS) -RTS"

test_js:
	$(CB) test $(ARGS) --test-options \
		"$(TEST-ARGS) --node --rerun-update +RTS -N$(TEST-JOBS) -RTS"

test_update:
	$(CB) test $(ARGS) --test-options \
		"$(TEST-ARGS) --accept +RTS -N$(TEST-JOBS) -RTS"

test_clean:
	rm -f test/*~
	rm -f test/*/output

rts:
	$(MK) -C rts

rts_install:
	$(MK) -C rts install

rts_clean:
	$(MK) -C rts clean

lib:
	$(MK) -C libs

lib_install:
	$(MK) -C libs install

lib_clean:
	$(MK) -C libs clean

lib_doc:
	+$(MK) -C libs doc

lib_doc_clean:
	+$(MK) -C libs doc_clean

relib: lib_clean
	$(CB) install $(CABALFLAGS)

linecount:
	wc -l src/Idris/*.hs src/Idris/Elab/*.hs src/Idris/Core/*.hs src/IRTS/*.hs src/Pkg/*.hs src/Util/*.hs

#Note: this doesn't yet link to Hackage properly
doc: dist/setup-config
	$(CB) haddock --hyperlink-source --html --hoogle --html-location="http://hackage.haskell.org/packages/archive/\$$pkg/latest/doc/html" --haddock-options="--title Idris"

user_docs: user_doc_html user_doc_pdf

user_doc_clean:
	$(MK) -C docs clean

user_doc_html:
	$(MK) -C docs html

user_doc_pdf:
	$(MK) -C docs latexpdf

fast:
	$(CB) install $(CABALFLAGS) --ghc-option=-O0

dist/setup-config:
	$(CB) configure $(CABALFLAGS)
