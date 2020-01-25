#!/usr/bin/env bash
${IDRIS:-idris} $@ --quiet --port none < input.in
${IDRIS:-idris} $@ -o basic025 basic025.idr

./basic025 input.in

rm -f basic025 *.ibc
