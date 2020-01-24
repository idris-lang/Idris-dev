#!/usr/bin/env bash
# Tests that documentation is generated for functions
${IDRIS:-idris} $@ --mkdoc test_functions.ipkg
[ -d test_functions_doc ] && echo "Functions are documented"
rm -rf *.ibc *_doc
