#!/usr/bin/env bash
${IDRIS:-idris} $@ totality022.idr --check
rm -f *.ibc
