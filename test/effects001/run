#!/usr/bin/env bash
${IDRIS:-idris} $@ -p effects test021.idr -o test021
${IDRIS:-idris} $@ -p effects test021a.idr -o test021a
./test021
./test021a
rm -f test021 test021a *.ibc
