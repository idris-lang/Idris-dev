#!/usr/bin/env bash
${IDRIS:-idris} $@ ffi007.idr -o ffi007 --cg-opt "ffi007.c"
./ffi007
rm -f ffi007 *.ibc
