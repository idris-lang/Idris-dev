-- ------------------------------------------------------------- [ Runners.idr ]
-- Module    : Runners.idr
-- Copyright : (c) The Idris Community.
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Given a series of tests, execute them and report results.
module Test.Unit.Runners

import Test.Unit.Display

%default total
%access export

namespace NonReporting
  ||| Run the given set of tests, but don't return the results.
  runTests : List (IO Bool) -> IO ()
  runTests Nil = do
           putStrLn "All Tests have been performed."
           putStrLn succLine
  runTests (t::ts) = do t; runTests ts

namespace Reporting
  ||| Run the given set of tests and return the results.
  runTests : List (IO Bool) -> IO (List Bool)
  runTests Nil = do
    putStrLn "All tests have been performed."
    putStrLn succLine
    pure Nil
  runTests (x::xs) = do
       r  <- x
       rs <- Reporting.runTests xs
       pure (r::rs)



-- --------------------------------------------------------------------- [ EOF ]
