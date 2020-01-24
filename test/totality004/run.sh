#!/usr/bin/env bash
${IDRIS:-idris} $@ totality004.idr -o totality004
./totality004
${IDRIS:-idris} $@ --check totality004a.idr 
rm -f totality004 *.ibc
