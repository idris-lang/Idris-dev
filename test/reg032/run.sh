#!/usr/bin/env bash
${IDRIS:-idris} $@ test028.idr -o test028
./test028
rm -f test028 test028.ibc
