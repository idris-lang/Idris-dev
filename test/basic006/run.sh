#!/usr/bin/env bash

${IDRIS:-idris} $@ test020.idr -o test020
${IDRIS:-idris} $@ test020a.idr --check --nocolor
./test020
rm -f test020 *.ibc
