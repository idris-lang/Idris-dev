#!/usr/bin/env bash
${IDRIS:-idris} $@ --quiet --port none --nocolor docs001.idr < input.in
rm *.ibc
