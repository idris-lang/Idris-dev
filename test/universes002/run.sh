#!/usr/bin/env bash
${IDRIS:-idris} $@ universes002.idr --check
rm -f *.ibc
