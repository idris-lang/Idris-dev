#!/usr/bin/env bash
${IDRIS:-idris} $@ -p pruviloj --nocolour --check --consolewidth 70 DataDef.idr
${IDRIS:-idris} $@ -p pruviloj --nocolour --check --consolewidth 70 Tacs.idr
${IDRIS:-idris} $@ -p pruviloj --nocolour --check --consolewidth 70 AgdaStyleReflection.idr
# Disabled due to excess memory consumption
# ${IDRIS:-idris} $@ -p pruviloj --nocolour --check --consolewidth 70 Deriving.idr
rm -f *.ibc
