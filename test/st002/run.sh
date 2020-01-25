#!/usr/bin/env bash
${IDRIS:-idris} $@ -p contrib test002.idr -o test002
echo "# test002:"
./test002
rm -f test002 *.ibc

