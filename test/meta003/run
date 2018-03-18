#!/usr/bin/env bash
${IDRIS:-idris} $@ --nocolour --check --consolewidth 70 BadDef.idr
${IDRIS:-idris} $@ --nocolour --consolewidth 70 -o meta003 Catch.idr
./meta003
rm -f meta003 *.ibc
