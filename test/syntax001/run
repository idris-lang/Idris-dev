#!/usr/bin/env bash
${IDRIS:-idris} $@ Syntax.idr --nocolour --check
${IDRIS:-idris} $@ SyntaxTest.idr --nocolour --check
rm -f *.ibc
