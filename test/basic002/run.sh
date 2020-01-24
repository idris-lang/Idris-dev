#!/usr/bin/env bash
${IDRIS:-idris} $@ --nocolour test006.idr -o test006
./test006
rm -f test006 test006.ibc
