#!/usr/bin/env bash
${IDRIS:-idris} $@ --nocolour --consolewidth 70 interfaces005.idr --check
${IDRIS:-idris} $@ --nocolour --consolewidth 70 interfaces005a.idr --check
${IDRIS:-idris} $@ --nocolour --consolewidth 70 interfaces005b.idr --check
rm -rf *.ibc
