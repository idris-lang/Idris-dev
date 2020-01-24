#!/usr/bin/env bash
${IDRIS:-idris} $@ test011.idr -o test011
./test011
rm -f test011 test011.ibc
