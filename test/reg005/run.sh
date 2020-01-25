#!/usr/bin/env bash
${IDRIS:-idris} $@ reg005.idr -o reg005
./reg005
rm -f reg005 *.ibc
