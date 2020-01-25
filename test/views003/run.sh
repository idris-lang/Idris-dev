#!/usr/bin/env bash
${IDRIS:-idris} $@ views003.idr -o views003 --warnreach
./views003 10000
rm -f views003 *.ibc
