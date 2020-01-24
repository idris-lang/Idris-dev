#!/usr/bin/env bash
# Tests that no documentation is built for empty and/or private-only namespaces
${IDRIS:-idris} $@ --mkdoc test_empty.ipkg
rm -rf *.ibc *_doc
