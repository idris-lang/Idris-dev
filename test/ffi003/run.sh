#!/usr/bin/env bash
${IDRIS:-idris} $@ --quiet --port none --nocolour test024.idr --exec main < input.in
rm -f *.ibc
