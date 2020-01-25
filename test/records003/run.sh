#!/usr/bin/env bash
${IDRIS:-idris} $@ records003.idr -o records003
./records003
rm -f records003 *.ibc
