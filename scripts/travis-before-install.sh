#!/bin/bash
# ------------------------------------------------- [ travis-before-install.sh ]
#
# The before install script used as part of the travis set up.
#
# ---------------------------------------------------------------------- [ EOH ]

set -ev

#  ---------------------------------------------- [ Local Copy of Travis Retry ]
#
# Common bash functions used by travis but not exposed or runnable as
# sub-commands. See:
#
# https://twitter.com/plexus/status/499194992632811520
#
ANSI_RED="\033[31;1m"
ANSI_GREEN="\033[32;1m"
ANSI_RESET="\033[0m"
ANSI_CLEAR="\033[0K"

travis_retry() {
  local result=0
  local count=1
  while [ $count -le 3 ]; do
    [ $result -ne 0 ] && {
      echo -e "\n${ANSI_RED}The command \"$@\" failed. Retrying, $count of 3.${ANSI_RESET}\n" >&2
    }
    "$@"
    result=$?
    [ $result -eq 0 ] && break
    count=$(($count + 1))
    sleep 1
  done

  [ $count -gt 3 ] && {
    echo -e "\n${ANSI_RED}The command \"$@\" failed 3 times.${ANSI_RESET}\n" >&2
  }

  return $result
}

#  -------------------------------------------------------------- [ The Script ]

unset CC
export PATH=/opt/ghc/$GHCVER/bin:/opt/cabal/$CABALVER/bin:$HOME/.cabal/bin:$PATH
env
mkdir -p ~/.local/bin
export PATH=$HOME/.local/bin:$PATH
travis_retry curl -L https://github.com/commercialhaskell/stack/releases/download/v0.1.4.0/stack-0.1.4.0-x86_64-linux.tar.gz | tar xz -C ~/.local/bin

#  --------------------------------------------------------------------- [ EOS ]
