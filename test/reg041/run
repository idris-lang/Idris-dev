#!/usr/bin/env bash
${IDRIS:-idris} $@ --quiet --port none ott.idr -e example
${IDRIS:-idris} $@ showu.idr -o reg040
./reg040
rm -f reg040 *.ibc
