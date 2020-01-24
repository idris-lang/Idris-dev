#!/usr/bin/env bash
${IDRIS:-idris} $@ effects004.idr -o effects004 -p effects
./effects004 < input.in
rm -f effects004 *.ibc
