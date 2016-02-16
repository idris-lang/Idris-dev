#!/usr/bin/env bash

${IDRIS:-idris} $@ Main.idr --nocolour --check && echo MAIN-PASS
${IDRIS:-idris} $@ Faulty.idr --nocolour --check && echo FAULTY-PASS
${IDRIS:-idris} $@ Multiple.idr --nocolour --check && echo MULTIPLE-PASS


rm -f *.ibc B/*.ibc 
