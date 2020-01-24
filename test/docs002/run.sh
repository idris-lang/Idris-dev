#!/usr/bin/env bash
${IDRIS:-idris} $@ --nobanner --nocolor --quiet --port none docs002.idr < input.in
rm *.ibc
