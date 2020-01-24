#!/usr/bin/env bash
${IDRIS:-idris} $@ test027.idr -o test027
./test027
rm -f test027 *.ibc
