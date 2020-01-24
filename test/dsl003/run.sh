#!/usr/bin/env bash
${IDRIS:-idris} $@ --nocolour --check DSLPi.idr -e test1 -e test2
rm -f *.ibc
