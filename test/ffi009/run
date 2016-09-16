#!/usr/bin/env bash
${IDRIS:-idris} $@ Bad.idr -o bad --cg-opt "ffi009.c" --cg-opt "-fno-strict-overflow"
${IDRIS:-idris} $@ Good.idr -o good --cg-opt "ffi009.c"
./good
rm -f *.ibc good
