#!/usr/bin/env bash

set -eu

TIMEOUT=../scripts/timeout

$TIMEOUT 20 "${IDRIS:-idris}" "$@" Main.idr --nocolour --check --warnreach -o basic010
$TIMEOUT 20  ./basic010

rm -f -- *.ibc basic010
