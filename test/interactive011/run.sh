#!/usr/bin/env bash

cd src
${IDRIS:-idris} "$@" --quiet --port none --indent-clause 4 Main.idr <../input.in

rm -f *.ibc
