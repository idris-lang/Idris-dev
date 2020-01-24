#!/usr/bin/env bash
### Test: IPKG executable names can be a quoted string
### containing a valid filename.
${IDRIS:-idris} $@ --build test.ipkg
rm -f *.ibc
rm -f 'quoting-allows-hyphens and spaces and fun stuff!'
