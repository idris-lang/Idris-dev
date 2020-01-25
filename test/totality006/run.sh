#!/usr/bin/env bash
${IDRIS:-idris} $@ totality006.idr --check
${IDRIS:-idris} $@ totality006a.idr --check
${IDRIS:-idris} $@ totality006b.idr --check
rm -f *.ibc
