#!/usr/bin/env bash
${IDRIS:-idris} $@ --check --nocolour WithPatsNoWith.idr
rm -f *.ibc
