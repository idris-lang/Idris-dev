#!/usr/bin/env bash
${IDRIS:-idris} $@ -o p005 primitives005.idr --nocolour
./p005
rm -f p005 *.ibc

