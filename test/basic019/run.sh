#!/usr/bin/env bash
${IDRIS:-idris} $@ basic019.idr -o basic019
./basic019
rm -f basic019 *.ibc
