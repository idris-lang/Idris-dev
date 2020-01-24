#!/usr/bin/env bash
${IDRIS:-idris} $@ interfaces007.idr -o interfaces007
./interfaces007
rm -f interfaces007 *.ibc
