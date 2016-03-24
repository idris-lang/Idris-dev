#!/usr/bin/env bash
${IDRIS:-idris} $@ test003a.lidr --check
${IDRIS:-idris} $@ test003.lidr -o test003
./test003
rm -f test003 test003.ibc Lit.ibc
