#!/usr/bin/env bash
${IDRIS:-idris} $@ --quiet --port none interactive004.idr < input.in
rm -f *.ibc
