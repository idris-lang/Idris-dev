#!/usr/bin/env bash

${IDRIS:-idris} $@ --build datatype.ipkg

${IDRIS:-idris} $@ --clean datatype.ipkg

${IDRIS:-idris} $@ -p datatype.ipkg
