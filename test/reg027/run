#!/usr/bin/env bash
${IDRIS:-idris} $@ reg027.idr -o reg027
./reg027
${IDRIS:-idris} $@ reg027a.idr --check
rm -f reg027 *.ibc
