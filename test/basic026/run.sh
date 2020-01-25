#!/usr/bin/env bash
${IDRIS:-idris} $@ basic026.idr -o basic026
./basic026
rm -f basic026 *.ibc
