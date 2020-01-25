#!/usr/bin/env bash
${IDRIS:-idris} $@ totality023.idr --check
rm -f *.ibc
