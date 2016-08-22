#!/usr/bin/env bash
${CC:-cc} -shared -fPIC nativetypes.c -o nativetypes.so
${IDRIS:-idris} $@ tutorial007.idr -o tutorial007
./tutorial007
rm -f tutorial007 *.ibc *.so sizefromc.txt
