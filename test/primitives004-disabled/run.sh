#!/usr/bin/env bash
${IDRIS:-idris} $@ -o primitives004 primitives004.idr --nocolour
./primitives004
rm -f primitives004 *.ibc
