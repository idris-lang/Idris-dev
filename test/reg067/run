#!/usr/bin/env bash
rm -f *.ibc reg067
${IDRIS:-idris} $@ reg067.idr -o reg067 --warnreach
./reg067
rm -f *.ibc reg067
