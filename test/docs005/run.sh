#!/usr/bin/env bash
${IDRIS:-idris} $@ --quiet --port none --nocolor docs005.idr < input.in
rm *.ibc
