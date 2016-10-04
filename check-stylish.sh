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
    # It takes a while to compile, let's not tax Travis' infrastructure for no
    # reason. We can't cache it via cabsnap because that's based on the install-
    # plan for Idris, which of course doesn't have stylish-haskell as a
    # dependency.
    STYLISH_EXE=$(mktemp)
    wget -O $STYLISH_EXE "https://s3-us-west-2.amazonaws.com/idris-travis-binaries/stylish-haskell"
    chmod +x $STYLISH_EXE
else
    STYLISH_EXE=stylish-haskell
fi


find . -name \*.hs -and \( -not -name Setup.hs \) | xargs $STYLISH_EXE -i > stylish-out 2>&1

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
