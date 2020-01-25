#!/usr/bin/env bash
${IDRIS:-idris} $@ --build test-pkg.ipkg
rm -f  *.ibc
${IDRIS:-idris} $@ --build test-pkg.ipkg --quiet
${IDRIS:-idris} $@ --build test-pkg.ipkg --logging-categories "elab" --log 1
${IDRIS:-idris} $@ --build malformed-package-name
${IDRIS:-idris} $@ --build non-existent-package.ipkg
${IDRIS:-idris} $@ --build non-existent-package-with-malformed-name
