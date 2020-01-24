#!/usr/bin/env bash
${IDRIS:-idris} $@ --quiet --port none --nocolour double-echo.idr < input.in
rm -f *.ibc
