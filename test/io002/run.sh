#!/usr/bin/env bash
${IDRIS:-idris} $@ test008.idr -o test008
./test008
rm -f test008 test008.ibc
