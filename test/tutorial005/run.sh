#!/usr/bin/env bash
${IDRIS:-idris} $@ tutorial005.idr --check
rm -f *.ibc
