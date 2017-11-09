-- ------------------------------------------------------------- [ Generic.idr ]
-- Module    : Generic.idr
-- Copyright : (c) The Idris Community
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Generic Tests
module Test.Unit.Generic

import Text.PrettyPrint.WL

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
  when (not res) $ do
     let errMsg = vcat [
           text errLine
         , text "An error occured" <+> colon
         , indent 2 $ text "Given" <+> colon
         , indent 4 $ text (show g)
         , indent 2 $ text "Expected" <+> colon
         , indent 4 $ text (show e)
         , text errLine]
     putStrLn $ Default.toString errMsg
  pure res

-- --------------------------------------------------------------------- [ EOF ]
