#!/usr/bin/env bash
${IDRIS:-idris} $@ totality017.idr --check
rm -f *.ibc
