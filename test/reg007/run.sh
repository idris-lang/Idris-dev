#!/usr/bin/env bash
${IDRIS:-idris} $@ --nocolour --check reg007.lidr
rm -f *.ibc
