#!/usr/bin/env bash
${IDRIS:-idris} $@ totality008.idr --check
rm -f *.ibc
