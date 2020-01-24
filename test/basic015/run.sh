#!/usr/bin/env bash
${IDRIS:-idris} $@ basic015.idr -o basic015
./basic015
rm -f basic015 *.ibc
