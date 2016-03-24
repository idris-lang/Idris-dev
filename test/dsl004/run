#!/usr/bin/env bash
${IDRIS:-idris} $@ Door0.idr --check
${IDRIS:-idris} $@ Door1.idr --check
${IDRIS:-idris} $@ Door2.idr --check
rm -f *.ibc
