#!/usr/bin/env bash
${IDRIS:-idris} $@ bignum001.idr -o bignum001
./bignum001
rm -f bignum001 *.ibc
