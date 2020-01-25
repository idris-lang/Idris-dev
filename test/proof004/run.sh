#!/usr/bin/env bash
${IDRIS:-idris} $@ --check test035.idr
rm -f *.ibc
