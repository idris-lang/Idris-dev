#!/usr/bin/env bash
${IDRIS:-idris} $@ --nocolour --consolewidth 70 interfaces002.idr -o interfaces002
./interfaces002
rm -f interfaces002 *.ibc
