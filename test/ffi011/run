#!/usr/bin/env bash
${IDRIS:-idris} $@ ffi011.idr --interface -o lib.js
node ./ffi011
rm -f *.ibc lib.js
