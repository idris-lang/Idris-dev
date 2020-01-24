#!/usr/bin/env bash
${IDRIS:-idris} $@ reg042 -o reg042 --warnreach
./reg042
rm -f reg042 *.ibc
