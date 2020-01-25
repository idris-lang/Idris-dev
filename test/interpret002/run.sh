#!/usr/bin/env bash
${IDRIS:-idris} $@ --quiet --port none --nocolour file-error.idr < input.in
rm -f *.ibc
