#!/usr/bin/env bash
${IDRIS:-idris} $@ totality011.lidr --check
rm -f *.ibc
