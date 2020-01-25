#!/usr/bin/env bash
${IDRIS:-idris} $@ test019.lidr -o test019
./test019
rm -f test019 *.ibc
