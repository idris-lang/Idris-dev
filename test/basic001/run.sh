#!/usr/bin/env bash
${IDRIS:-idris} $@ reg005.idr -o reg005
${IDRIS:-idris} $@ basic001a.idr -o basic001a
./reg005
./basic001a
rm -f reg005 basic001a *.ibc
