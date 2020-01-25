#!/usr/bin/env bash
${IDRIS:-idris} $@ basic011.idr -p contrib -o basic011
./basic011
rm -f basic011 *.ibc
