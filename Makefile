install: .PHONY
	cabal install

pinstall: .PHONY
	cabal configure --enable-executable-profiling
	cabal install --enable-executable-profiling

build: .PHONY
	cabal build

configure: .PHONY
	cabal configure

test : .PHONY
	make -C test

linecount : .PHONY
	wc -l src/Idris/*.hs src/Core/*.hs

.PHONY:

