#!/usr/bin/env bash
${IDRIS:-idris} $@ --nocolour --check ClaimAndUnfocus.idr
rm -f *.ibc
