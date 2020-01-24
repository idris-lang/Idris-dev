#!/usr/bin/env bash
${IDRIS:-idris} $@ reg024.idr -o reg024
./reg024
rm -f reg024 *.ibc
