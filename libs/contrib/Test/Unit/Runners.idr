-- ------------------------------------------------------------- [ Runners.idr ]
-- Module    : Runners.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module Test.Unit.Runners

import Test.Unit.Display

%default total
%access export

namespace NonReporting
  runTests : List (IO a) -> IO ()
  runTests Nil     = do putStrLn "All Tests have passed"; putStrLn succLine
  runTests (t::ts) = do t; runTests ts

namespace Reporting
  runTests : List (IO a) -> IO (List a)
  runTests Nil     = pure Nil
  runTests (x::xs) = do
       r  <- x
       rs <- Reporting.runTests xs
       pure (r::rs)



-- --------------------------------------------------------------------- [ EOF ]
