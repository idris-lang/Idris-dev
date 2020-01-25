#!/usr/bin/env bash
${IDRIS:-idris} $@ basic017.idr --check --nocolor
${IDRIS:-idris} $@ basic017a.idr --check --nocolor
rm -f *.ibc
