#!/usr/bin/env bash

${IDRIS:-idris} $@ --quiet --port none --indent-with 8 interactive001.idr < input.in

rm -f *.ibc
