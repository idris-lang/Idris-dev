#!/usr/bin/env bash

set -e

if [ -n "$TRAVIS" ];
then
    mkdir -p ~/.local/bin
    export PATH=$HOME/.local/bin:/opt/ghc/$GHCVER/bin:$PATH
    curl --retry 3 -L https://www.stackage.org/stack/linux-x86_64 | tar xz --wildcards --strip-components=1 -C ~/.local/bin '*/stack'
    stack config set system-ghc --global true
    stack install --resolver "lts-$STACKVER" stylish-haskell --no-terminal
fi


find . -name \*.hs -and \( -not \( -name Setup.hs -or -path ./.cabal-sandbox/\* -or -path ./dist/\* \) \) | xargs stylish-haskell -i > stylish-out 2>&1

# It doesn't do exit codes properly, so we just check if it outputted anything.
if [ -s stylish-out ];
then
    echo "Stylish-haskell reported an error :("
    cat stylish-out
    exit 1
fi

rm stylish-out

if git status --porcelain|grep .; # true if there was any output
then
    echo "Git tree is dirty after stylizing.";
    if [ -n "$TRAVIS" ];
    then
        echo "Since we're on Travis, this is a build failure."
        echo "Run ./stylize.sh to stylize your tree and push the changes."
        exit 1
    fi
else
    echo "Stylish didn't change anything :)"
    exit 0;
fi
