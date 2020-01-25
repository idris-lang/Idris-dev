#!/usr/bin/env bash
${IDRIS:-idris} $@ --quiet --port none reg075.idr < input.in
rm -f *.ibc
