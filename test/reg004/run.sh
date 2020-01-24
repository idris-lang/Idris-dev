#!/usr/bin/env bash
${IDRIS:-idris} $@ reg004.idr -o reg004
./reg004
rm -f reg004 *.ibc
