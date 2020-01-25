#!/usr/bin/env bash
${IDRIS:-idris} $@ totality016.idr --check
rm -f *.ibc
