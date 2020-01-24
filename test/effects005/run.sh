#!/usr/bin/env bash
${IDRIS:-idris} $@ defaultLogger.idr -o default -p effects
./default
${IDRIS:-idris} $@ categoryLogger.idr -o category -p effects
./category
rm -f default category *.ibc
