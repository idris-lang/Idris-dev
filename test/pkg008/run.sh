#!/usr/bin/env bash

${IDRIS:-idris} $@ --build maths.ipkg
${IDRIS:-idris} $@ --testpkg maths.ipkg | grep -v -e "idris"

# Idris only appears in the randomly generated name of test so we grep
# to remove it to make output consistent.

${IDRIS:-idris} $@ --clean maths.ipkg

${IDRIS:-idris} $@ -p maths
