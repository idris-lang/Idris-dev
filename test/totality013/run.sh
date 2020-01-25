#!/usr/bin/env bash
${IDRIS:-idris} $@ totality013.idr --check
${IDRIS:-idris} $@ totality013a.idr --check
rm -f *.ibc
