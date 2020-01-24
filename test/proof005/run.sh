#!/usr/bin/env bash
${IDRIS:-idris} $@ --check DefaultArgSubstitutionSuccess.idr
rm -f *.ibc
