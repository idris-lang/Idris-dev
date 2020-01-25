#!/usr/bin/env bash
${IDRIS:-idris} $@ --nocolour --quiet --port none interactive005.idr --consolewidth 70 < input.in
rm -f *.ibc
rm -f hello.bytecode
rm -f hello
rm -f a.out
