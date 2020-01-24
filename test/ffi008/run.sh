#!/usr/bin/env bash
${IDRIS:-idris} $@ ffi008.idr -o ffi008 -p contrib --cg-opt "ffi008.c"
./ffi008
rm -f ffi008 *.ibc
