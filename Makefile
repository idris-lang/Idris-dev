install: .PHONY
	cabal install
	make -C lib check

pinstall: .PHONY
	cabal configure --enable-executable-profiling
	cabal install --enable-executable-profiling
	make -C lib check

build: .PHONY
	cabal build

configure: .PHONY
	cabal configure

test : .PHONY
	make -C test

linecount : .PHONY
	wc -l src/Idris/*.hs src/Core/*.hs

.PHONY:

