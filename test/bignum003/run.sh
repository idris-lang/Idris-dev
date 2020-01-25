#!/usr/bin/env bash
${IDRIS:-idris} $@ bignum003.idr -o bignum003
./bignum003
rm -f bignum003 *.ibc
