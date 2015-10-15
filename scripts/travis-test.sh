#!/bin/bash
# ---------------------------------------------------------- [ travis-test.sh ]
# The test script used as part of the travis set up.
#
# --------------------------------------------------------------------- [ EOH ]

set -ev

if [[ "$STACKTEST" == "stack_test" ]];
then
    stack --no-terminal --system-ghc build;
else
    cabal configure -f FFI -f CI;
    cabal build;
    cabal copy;
    cabal register;
    if [[ "$TESTS" == "test_c" ]];
    then
        cppcheck -i 'mini-gmp.c' rts;
    fi
    for test in $TESTS;
    do
        echo "make -j2 $test";
        make -j2 $test;
    done
fi

#  --------------------------------------------------------------------- [ EOS ]
