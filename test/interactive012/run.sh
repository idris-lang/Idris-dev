#!/usr/bin/env bash
${IDRIS:-idris} $@ --nocolour --consolewidth 70 --quiet --port none interactive012.idr < input.in
rm -f *.ibc
