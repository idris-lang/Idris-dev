#!/usr/bin/env bash
${IDRIS:-idris} $@ ffi012.idr --interface -o lib.js
node ./ffi012
rm -f *.ibc lib.js
