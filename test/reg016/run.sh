#!/usr/bin/env bash
${IDRIS:-idris} $@ reg016.idr -o reg016
./reg016
rm -f reg016 *.ibc
