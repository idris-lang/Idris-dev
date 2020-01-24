#!/usr/bin/env bash
${IDRIS:-idris} $@ basic022.idr -o basic022
./basic022
rm -f basic022 *.ibc
