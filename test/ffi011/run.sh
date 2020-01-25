#!/usr/bin/env bash
${IDRIS:-idris} $@ ffi011.idr --interface -o lib.js
node ./ffi011.js
rm -f *.ibc lib.js
