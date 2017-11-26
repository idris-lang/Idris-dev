#!/usr/bin/env bash
${IDRIS:-idris} $@ -p contrib test001.idr -o test001
echo "# test001:"
./test001
rm -f test001 *.ibc

