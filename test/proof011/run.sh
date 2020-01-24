#!/usr/bin/env bash
${IDRIS:-idris} $@ proof011.idr --nocolour --check
${IDRIS:-idris} $@ proof011a.idr --nocolour --check
rm -f *.ibc
