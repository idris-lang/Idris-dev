#!/usr/bin/env bash
${IDRIS:-idris} $@ directives001.idr --check --nocolour

rm -f directives001 *.ibc
