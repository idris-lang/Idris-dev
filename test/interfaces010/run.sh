#!/usr/bin/env bash
${IDRIS:-idris} $@ --nocolour --consolewidth 70 interfaces010.idr --check
rm -f interfaces010 *.ibc
