#!/usr/bin/env bash
${IDRIS:-idris} $@ --nocolour --quiet --port none Test.idr < input.in
rm -f *.ibc
