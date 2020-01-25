#!/usr/bin/env bash
${CC:-cc} -c -O2 -o array.o array.c $(${IDRIS:-idris} --include)
${IDRIS:-idris} $@ -o load-test load-test.idr --nocolour --warnreach
./load-test
rm -f load-test *.o *.ibc
rm -f Data/*.ibc
