#!/usr/bin/env bash
${IDRIS:-idris} $@ ffi006.idr --interface -o ffi006.o
${CC:=cc} ffi006.c ffi006.o `${IDRIS:-idris} $@ --include` `${IDRIS:-idris} $@ --link` -o ffi006
./ffi006
rm -f ffi006 *.ibc *.o *.h
