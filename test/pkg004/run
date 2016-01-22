#!/usr/bin/env bash
### Test: IPKG executable names CANNOT include a directory separator.
# TODO: Verify that a name like "a/b\c" is rejected by both *NIX and Windows
# (assuming these tests get run on Windows).
${IDRIS:-idris} $@ --build test.ipkg
rm -f *.ibc
