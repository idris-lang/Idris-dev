#!/usr/bin/env bash
${IDRIS:-idris} $@ bignum002.idr -o bignum002
./bignum002
rm -f bignum002 *.ibc
