#!/usr/bin/env bash
${IDRIS:-idris} $@ test002.idr --check --noprelude --consolewidth 70
rm -f *.ibc
