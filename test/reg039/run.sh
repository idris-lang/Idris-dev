#!/usr/bin/env bash

set -eu

TIMEOUT=../scripts/timeout

$TIMEOUT 60 "${IDRIS:-idris}" "$@" --nocolour reg039.idr --exec go
rm -f *.ibc
