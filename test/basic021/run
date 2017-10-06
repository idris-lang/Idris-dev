#!/usr/bin/env bash
${IDRIS:-idris} $@ basic021.idr -o basic021
${IDRIS:-idris} $@ basic021_2.idr -o basic021_2
./basic021
./basic021_2
rm -f basic021 basic021_2 *.ibc
