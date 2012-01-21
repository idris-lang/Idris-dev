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

relib: .PHONY
	make -C lib clean
	make -C lib IDRIS=../dist/build/idris/idris

linecount : .PHONY
	wc -l src/Idris/*.hs src/Core/*.hs

.PHONY:

