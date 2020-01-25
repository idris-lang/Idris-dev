#!/usr/bin/env bash
${IDRIS:-idris} $@ reg045.idr -o reg045
./reg045
rm -f reg045 *.ibc
