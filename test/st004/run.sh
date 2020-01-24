#!/usr/bin/env bash
${IDRIS:-idris} $@ -p contrib test004.idr -o test004
echo "# test004:"
./test004
rm -f test004 *.ibc

