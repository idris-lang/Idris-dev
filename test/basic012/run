#!/usr/bin/env bash
${IDRIS:-idris} $@ basic012.idr -o basic012
./basic012
${IDRIS:-idris} $@ basic012a.idr --check
rm -f basic012 *.ibc
