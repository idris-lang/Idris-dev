#!/usr/bin/env bash
${IDRIS:-idris} $@ --quiet --port none --nocolor delab001.idr < input.in
rm -f *.ibc
