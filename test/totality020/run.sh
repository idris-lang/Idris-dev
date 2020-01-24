#!/usr/bin/env bash
${IDRIS:-idris} $@ totality020.idr --check
rm -f *.ibc
