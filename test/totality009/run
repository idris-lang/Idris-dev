#!/usr/bin/env bash
OPTS="--consolewidth infinite --nocolour"
${IDRIS:-idris} $@ $OPTS --check TestLambdaImpossible
${IDRIS:-idris} $@ $OPTS --check --warnpartial TestLambdaPossible
${IDRIS:-idris} $@ $OPTS --check TestLambdaPossible2
rm -f *.ibc
