#!/usr/bin/env bash

${IDRIS:-idris} $@ Postulate.idr -o postulate
./postulate
rm -f postulate *.ibc
