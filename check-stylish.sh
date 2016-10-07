#!/bin/bash

set -e

function fail_maybe_explain {
    if [ -n "$TRAVIS" ];
    then
        echo "Run ./check-stylish.sh locally to stylize your files / debug this"
    fi
    exit 1
}

if [ -n "$TRAVIS" ];
then
    mkdir -p ~/.local/bin
    export PATH=$HOME/.local/bin:/opt/ghc/8.0.1/bin:$PATH
    curl --retry 3 -L https://www.stackage.org/stack/linux-x86_64 | tar xz --wildcards --strip-components=1 -C ~/.local/bin '*/stack'
    stack install --resolver lts-7.2 stylish-haskell --no-terminal
fi


find . -name \*.hs -and \( -not -name Setup.hs \) | xargs stylish-haskell -i > stylish-out 2>&1

# It doesn't do exit codes properly, so we just check if it outputted anything.
if [ -s stylish-out ];
then
    echo "Stylish-haskell reported an error :("
    cat stylish-out
    fail_maybe_explain
fi

rm stylish-out

if git status --porcelain|grep .; # true if there was any output
then
    echo "Running stylish-haskell changed 1 or more files :(";
    fail_maybe_explain
else
    echo "Stylish is happy :)";
    exit 0;
fi
