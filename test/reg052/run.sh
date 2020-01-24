#!/usr/bin/env bash
${IDRIS:-idris} $@ -o reg052 reg052.idr
./reg052
rm -f reg052 *.ibc
