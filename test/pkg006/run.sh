#!/usr/bin/env bash
### Test: Launch REPL, IPKG executable without main.
${IDRIS:-idris} $@ --repl test.ipkg
