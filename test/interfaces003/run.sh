#!/usr/bin/env bash
${IDRIS:-idris} $@ --nocolour --consolewidth 70 interfaces003.idr -o interfaces003
./interfaces003
rm -f interfaces003 *.ibc
