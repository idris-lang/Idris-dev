#!/usr/bin/env bash
${IDRIS:-idris} $@ --nocolour --consolewidth 70 interfaces006.idr --noprelude --check
rm -rf *.ibc
