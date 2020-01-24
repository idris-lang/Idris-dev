#!/usr/bin/env bash
${IDRIS:-idris} $@ FunErrTest.idr --nocolour --check
rm -f *.ibc
