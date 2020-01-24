#!/usr/bin/env bash
${IDRIS:-idris} $@ test005.idr -o test005
./test005
${IDRIS:-idris} $@ substring.idr -o substring
./substring < input.in
rm -f test005 substring *.ibc
