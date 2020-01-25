#!/usr/bin/env bash
${IDRIS:-idris} $@ -p contrib --nobanner --nocolor --port none < input.in | perl -pe 's-Data\\Z-Data/Z-g'
