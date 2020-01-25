#!/usr/bin/env bash
# Tests that documentation is generated for interfaces
${IDRIS:-idris} $@ --mkdoc test_interfaces.ipkg
[ -d test_interfaces_doc ] && echo "Interfaces are documented"
rm -rf *.ibc *_doc
