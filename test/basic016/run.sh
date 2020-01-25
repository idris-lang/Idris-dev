#!/usr/bin/env bash
${IDRIS:-idris} $@ CycleA.idr --nocolour --check
rm -f *.ibc
