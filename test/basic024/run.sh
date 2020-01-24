#!/usr/bin/env bash

${IDRIS:-idris} $@ --quiet --port none < input.in
${IDRIS:-idris} $@ basic024.idr -o basic024

./basic024

rm -f basic024 *.ibc
