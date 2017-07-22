#!/usr/bin/env bash
${IDRIS:-idris} $@ regression003.idr -o regression003
./regression003
rm -f regression003 *.ibc
