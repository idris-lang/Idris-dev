#!/usr/bin/env bash
echo "test" > remove.me
${IDRIS:-idris} $@ --quiet --port none ffi013.idr -o ffi013
./ffi013
if [ -f "remove.me" ]; then
    echo "still exists"
else 
    echo "confirmed"
fi
echo "test2" > remove.me
${IDRIS:-idris} $@ --quiet --port none --nocolour ffi013.idr --exec main
if [ -f "remove.me" ]; then
    echo "still exists"
else 
    echo "confirmed"
fi
rm -f ffi013 remove.me *.ibc
