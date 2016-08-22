#!/usr/bin/env bash
${IDRIS:-idris} $@ --nocolour tutorial006a.idr --check
${IDRIS:-idris} $@ --nocolour tutorial006b.idr --check
${IDRIS:-idris} $@ --nocolour tutorial006c.idr -p effects --check
rm -f *.ibc
