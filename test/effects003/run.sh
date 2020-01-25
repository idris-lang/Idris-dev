#!/usr/bin/env bash
${IDRIS:-idris} $@ hangman.idr --nocolour -p effects -o hangman
./hangman < input.in
rm -f hangman *.ibc
