#!/usr/bin/env bash
${IDRIS:-idris} $@ views001.idr -o views001
./views001
${IDRIS:-idris} $@ views001a.idr -o views001a
./views001a
rm -f views001 views001a *.ibc
