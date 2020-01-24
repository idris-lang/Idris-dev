#!/usr/bin/env bash
${IDRIS:-idris} $@ test009.idr -o test009
./test009
rm -f test009 test009.ibc
