#!/usr/bin/env bash
${IDRIS:-idris} $@ totality025.idr --check
rm -f *.ibc
