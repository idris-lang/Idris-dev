#!/usr/bin/env bash
${IDRIS:-idris} $@ --quiet --port none test023.idr -o test023
rm -f test023 *.ibc
