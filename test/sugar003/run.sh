#!/usr/bin/env bash
${IDRIS:-idris} $@ test013.idr -o test013
./test013
rm -f test013 test013.ibc
