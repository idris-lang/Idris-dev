#!/usr/bin/env bash
${IDRIS:-idris} $@ --quiet --port none --nocolour --consolewidth 70 InterfaceName.idr < input.in
rm -f *.ibc
