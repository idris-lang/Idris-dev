#!/usr/bin/env bash
${IDRIS:-idris} $@ --quiet --port none interactive003.idr < input.in
rm -f *.ibc
