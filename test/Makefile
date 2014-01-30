.PHONY: test test_java test_js update diff distclean $(TESTS)

TESTS = $(sort $(patsubst %/,%.test,$(wildcard */)))

test: $(TESTS)

%.test:
	@perl ./runtest.pl $(patsubst %.test,%,$@)

test_java:
	perl ./runtest.pl all --codegen Java

test_js:
	@perl ./runtest.pl without reg029 reg031 test004 test014 test018 test021 test025 test033 --codegen node

test_llvm:
	@perl ./runtest.pl without test018 test033 --codegen llvm

update:
	/usr/bin/env perl ./runtest.pl all -u

diff:
	/usr/bin/env perl ./runtest.pl all -d

distclean:
	rm -f *~
	rm -f */output

