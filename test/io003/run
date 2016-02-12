#!/usr/bin/env bash
${IDRIS:-idris} $@ test018.idr -p contrib -o test018
${IDRIS:-idris} $@ test018a.idr -p contrib -o test018a
./test018
#./test018a
rm -f test018 test018a *.ibc
