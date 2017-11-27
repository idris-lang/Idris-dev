#!/usr/bin/env bash
${IDRIS:-idris} $@ -p contrib test006.idr -o test006
echo "# test006:"
./test006
cat writeStringTestFile
rm -f test006 writeStringTestFile *.ibc
