#!/usr/bin/env bash
# Tests that documentation is generated for data types
${IDRIS:-idris} $@ --mkdoc test_datatypes.ipkg
[ -d test_datatypes_doc ] && echo "Data types are documented"
rm -rf *.ibc *_doc
