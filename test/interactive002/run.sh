#!/usr/bin/env bash
${IDRIS:-idris} $@ --quiet --port none interactive002.idr < input.in
rm -f *.ibc
