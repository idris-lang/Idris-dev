#!/usr/bin/env bash
${IDRIS:-idris} $@ --quiet --port none interactive014.idr < input.in
rm -f *.ibc
