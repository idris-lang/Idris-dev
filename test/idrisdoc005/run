#!/usr/bin/env bash
# Tests that references to other namespaces are traced
${IDRIS:-idris} $@ --mkdoc test_tracing.ipkg
[ -f test_tracing_doc/docs/TestTracing.html ] && echo "TestTracing: Check"
[ -f test_tracing_doc/docs/Prelude.Bool.html ] && echo "Prelude.Bool: Check"
rm -rf *.ibc *_doc
