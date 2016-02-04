.PHONY: test test_js time update diff distclean $(TESTS)

TESTS = $(sort $(patsubst %/,%.test,$(wildcard */)))

test: $(TESTS)


info: runtest
	@./runtest all

%.test: runtest
	@./runtest $(patsubst %.test,%,$@) -q

test_js: runtest
	@./runtest without sugar004 reg029 reg052 io001 dsl002 io003 effects001 effects002 basic007 basic011 ffi006 primitives005 opts --codegen node

update: runtest
	@./runtest all -u

diff: runtest
	@./runtest all -d

time: runtest
	@./runtest all -t

distclean:
	@rm runtest
	@rm -f *~
	@rm -f */output


runtest:
	@ghc --make runtest.hs
	@rm runtest.o runtest.hi
