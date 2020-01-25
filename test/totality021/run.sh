#!/usr/bin/env bash
${IDRIS:-idris} $@ totality021.idr --check
${IDRIS:-idris} $@ totality021a.idr --check
rm -f *.ibc
