#!/usr/bin/env bash
${IDRIS:-idris} $@ -p contrib test005.idr -o test005
echo "# test005:"
./test005
cat writeTestFile
rm -f test005 writeTestFile *.ibc

