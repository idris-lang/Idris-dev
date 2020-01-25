#!/usr/bin/env bash
${IDRIS:-idris} $@ --quiet --port none Top.idr < input.in
rm -f *.ibc
