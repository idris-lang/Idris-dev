#!/usr/bin/env bash

# %lib C "nuyahcha"
# %lib C "mohgiide"
# %lib C "apeekair"
# %flag C "-Wl,-leeraimam -Wl,-lrahhahwi -Wl,-lgoocheiv"

${IDRIS:-idris} $@ -o directives003 directives003.idr \
    | tr ' ,"' '\n' \
    | sed 's/-l//' \
    | grep -E 'nuyahcha|mohgiide|apeekair|eeraimam|rahhahwi|goocheiv'

rm -f directives003 *.ibc
