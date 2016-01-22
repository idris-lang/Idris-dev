#!/usr/bin/env bash
${IDRIS:-idris} $@ totality005.idr --total --check
${IDRIS:-idris} $@ totality005.idr -o totality005
./totality005
rm -f totality005 *.ibc
