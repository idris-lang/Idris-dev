#!/usr/bin/env bash
${IDRIS:-idris} $@ -p contrib test007.idr -o test007
echo "# test007:"
./test007
cat writeFileTestFile
rm -f test007 writeFileTestFile *.ibc
