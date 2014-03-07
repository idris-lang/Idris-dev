.PHONY: test test_java test_js update diff distclean $(TESTS)

TESTS = $(sort $(patsubst %/,%.test,$(wildcard */)))

test: $(TESTS)

%.test:
	@perl ./runtest.pl $(patsubst %.test,%,$@)

test_java:
	perl ./runtest.pl without sugar004 buffer001 --codegen Java

test_js:
	@perl ./runtest.pl without sugar004 reg029 io001 dsl002 io003 effects001 effects002 buffer001 bounded001 --codegen node

test_llvm:
	@perl ./runtest.pl without sugar004 io003 buffer001 --codegen llvm

update:
	/usr/bin/env perl ./runtest.pl all -u

diff:
	/usr/bin/env perl ./runtest.pl all -d

distclean:
	rm -f *~
	rm -f */output

