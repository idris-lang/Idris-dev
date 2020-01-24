#!/usr/bin/env bash
${IDRIS:-idris} $@ folding001.idr -o folding001
./folding001
rm -f folding001 *.ibc
