#!/usr/bin/env bash
${IDRIS:-idris} $@ --nocolour --check DefaultArgUnknownName.idr
rm -f *.ibc
