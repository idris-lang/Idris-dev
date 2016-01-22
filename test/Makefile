.PHONY: test test_js time update diff distclean $(TESTS)


test:
	/usr/bin/env perl ./runtest.pl all

%.test:
	@perl ./runtest.pl $(patsubst %.test,%,$@)

test_js:
	@perl ./runtest.pl without sugar004 reg029 reg052 io001 dsl002 io003 effects001 effects002 basic007 basic011 ffi006 --codegen node

update:
	/usr/bin/env perl ./runtest.pl all -u

diff:
	/usr/bin/env perl ./runtest.pl all -d

time:
	/usr/bin/env perl ./runtest.pl all -t

distclean:
	rm -f *~
	rm -f */output
