#!/bin/bash
# -------------------------------------------------------- [ travis-install.sh ]
#
# Tee install script used as part of the travis set up.
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

#  ------------------------------------------------------------------- [ Setup ]

cabal --version
echo "$(ghc --version) [$(ghc --print-project-git-commit-id 2> /dev/null || echo '?')]"

if [ -f $HOME/.cabal/packages/hackage.haskell.org/00-index.tar.gz ];
then
    zcat $HOME/.cabal/packages/hackage.haskell.org/00-index.tar.gz >
         $HOME/.cabal/packages/hackage.haskell.org/00-index.tar;
fi

travis_retry cabal update -v

#  ---------------------------------------------------------- [ Do The Install ]

# Run build with 2 parallel jobs.  The container environment reports
# 16 cores, causing cabal's default configuration (jobs: $ncpus) to
# run into the GHC #9221 bug which can result in longer build-times.

sed -i -r 's/(^jobs:).*/\1 2/' $HOME/.cabal/config
cabal install -f FFI --only-dependencies --enable-tests --dry -v > installplan.txt
sed -i -e '1,/^Resolving /d' installplan.txt; cat installplan.txt


#  ---------------------------------------------------------- [ Package Checks ]
#
# check whether current requested install-plan matches cached package-db snapshot

if diff -u installplan.txt $HOME/.cabsnap/installplan.txt;
then
    echo "cabal build-cache HIT";
    rm -rfv .ghc;
    cp -a $HOME/.cabsnap/ghc $HOME/.ghc;
    cp -a $HOME/.cabsnap/lib $HOME/.cabsnap/share $HOME/.cabsnap/bin $HOME/.cabal/;
else
    echo "cabal build-cache MISS";
    rm -rf $HOME/.cabsnap;
    mkdir -p $HOME/.ghc $HOME/.cabal/lib $HOME/.cabal/share $HOME/.cabal/bin;
    cabal install -f FFI --only-dependencies --enable-tests;
fi

#  ------------------------------------------------------- [ Package-DB Saving ]
#
# snapshot package-db on cache miss

if [ ! -d $HOME/.cabsnap ];
then
    echo "snapshotting package-db to build-cache";
    mkdir $HOME/.cabsnap;
    cp -a $HOME/.ghc $HOME/.cabsnap/ghc;
    cp -a $HOME/.cabal/lib $HOME/.cabal/share $HOME/.cabal/bin installplan.txt $HOME/.cabsnap/;
fi

#  --------------------------------------------------------------------- [ EOS ]
