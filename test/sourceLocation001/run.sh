#!/usr/bin/env bash
${IDRIS:-idris} $@ --nocolour SourceLoc.idr -o sourceLocation001
./sourceLocation001
rm -f sourceLocation001 *.ibc
