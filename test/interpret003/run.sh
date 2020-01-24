#!/usr/bin/env bash
${IDRIS:-idris} $@ --quiet --port none --nocolour interpret003.idr < input.in
rm -f *.ibc
