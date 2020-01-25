#!/usr/bin/env bash
${IDRIS:-idris} $@ --nocolour --consolewidth 70 interfaces009.idr --noprelude --check
rm -f interfaces009 *.ibc
