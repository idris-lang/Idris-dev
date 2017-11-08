-- ------------------------------------------------------------- [ Generic.idr ]
-- Module    : Generic.idr
-- Copyright : (c) The Idris Community
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Generic Tests
module Test.Unit.Generic

import Test.Unit.Display

%default total
%access export

||| Run a generic test.
|||
||| @title     Optional Test title
||| @given     The given string to parse
||| @expected  The expected result
||| @tFunc     The testing function to compare the results.
genericTest : Show a
           => (title : Maybe String)
           -> (given : a)
           -> (expected : a)
           -> (tFunc : a -> a -> Bool)
           -> IO Bool
genericTest title g e eq = do
  putStrLn $ unwords ["Test:" , fromMaybe "Unnamed Test" title]
  let res = eq g e
  when (not res) $ with List do
     putStrLn $ unwords [
             errLine
           , "\n"
           , "Error:\n\n"
           , "Given:\n\t"
           , show g
           , "\n"
           , "Expected:\n\t"
           , show e
           , "\n"
           , errLine
           , "\n"
           ]
  pure res

-- --------------------------------------------------------------------- [ EOF ]
