#!/usr/bin/env bash
${IDRIS:-idris} $@ --check --nocolour error005.idr
rm -f *.ibc
