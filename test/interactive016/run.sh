#!/usr/bin/env bash

cp src/interactive016.idr .
${IDRIS:-idris} "$@" --quiet --port none interactive016.idr < input.in

cat interactive016.idr

rm -f *.ibc interactive016.idr
