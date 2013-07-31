TESTS = $(sort $(patsubst %/,%.test,$(wildcard */)))

test: $(TESTS)

%.test:
	@perl ./runtest.pl $(patsubst %.test,%,$@)

test_java:
	perl ./runtest.pl all --codegen Java

test_js:
	@perl ./runtest.pl reg001 --codegen node
	@perl ./runtest.pl reg002 --codegen node
	@perl ./runtest.pl reg003 --codegen node
	@perl ./runtest.pl reg004 --codegen node
	@perl ./runtest.pl reg005 --codegen node
	@perl ./runtest.pl reg006 --codegen node
	@perl ./runtest.pl reg007 --codegen node
	@perl ./runtest.pl reg008 --codegen node
	@perl ./runtest.pl reg009 --codegen node
	@perl ./runtest.pl reg010 --codegen node
	@perl ./runtest.pl reg011 --codegen node
	@perl ./runtest.pl reg012 --codegen node
	@perl ./runtest.pl reg013 --codegen node
	@perl ./runtest.pl reg014 --codegen node
	@perl ./runtest.pl reg015 --codegen node
	@#perl ./runtest.pl reg016 --codegen node
	@perl ./runtest.pl reg017 --codegen node
	@perl ./runtest.pl reg018 --codegen node
	@perl ./runtest.pl reg019 --codegen node
	@perl ./runtest.pl reg020 --codegen node
	@perl ./runtest.pl test001 --codegen node
	@perl ./runtest.pl test002 --codegen node
	@perl ./runtest.pl test003 --codegen node
	@#perl ./runtest.pl test004 --codegen node
	@perl ./runtest.pl test005 --codegen node
	@perl ./runtest.pl test006 --codegen node
	@perl ./runtest.pl test007 --codegen node
	@perl ./runtest.pl test008 --codegen node
	@perl ./runtest.pl test009 --codegen node
	@perl ./runtest.pl test010 --codegen node
	@perl ./runtest.pl test011 --codegen node
	@perl ./runtest.pl test012 --codegen node
	@perl ./runtest.pl test013 --codegen node
	@#perl ./runtest.pl test014 --codegen node
	@perl ./runtest.pl test015 --codegen node
	@perl ./runtest.pl test016 --codegen node
	@perl ./runtest.pl test017 --codegen node
	@#perl ./runtest.pl test018 --codegen node
	@perl ./runtest.pl test019 --codegen node
	@perl ./runtest.pl test020 --codegen node
	@#perl ./runtest.pl test021 --codegen node
	@perl ./runtest.pl test022 --codegen node
	@perl ./runtest.pl test023 --codegen node
	@perl ./runtest.pl test024 --codegen node
	@#perl ./runtest.pl test025 --codegen node
	@perl ./runtest.pl test026 --codegen node
	@perl ./runtest.pl test027 --codegen node
	@perl ./runtest.pl test028 --codegen node

update:
	perl ./runtest.pl all -u

diff:
	perl ./runtest.pl all -d

distclean:
	rm -f *~
	rm -f */output

.phony: test test_java test_js update diff distclean $(TESTS)
