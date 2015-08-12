.PHONY: test test_java test_js update diff distclean $(TESTS)

TESTS = $(sort $(patsubst %/,%.test,$(wildcard */)))

test: $(TESTS)

%.test:
	@perl ./runtest.pl $(patsubst %.test,%,$@)

test_js:
	@perl ./runtest.pl without sugar004 reg029 reg052 io001 dsl002 io003 effects001 effects002 basic007 basic011 ffi006 --codegen node

update:
	/usr/bin/env perl ./runtest.pl all -u

diff:
	/usr/bin/env perl ./runtest.pl all -d

distclean:
	rm -f *~
	rm -f */output
