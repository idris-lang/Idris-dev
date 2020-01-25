#!/usr/bin/env bash
${IDRIS:-idris} $@ --quiet --port none interactive013.idr < input.in
rm -f *.ibc
