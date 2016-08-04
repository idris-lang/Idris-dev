module Main where

import Control.Monad
import Data.Char (isLetter)
import Data.Typeable
import Data.Proxy
import Data.List
import qualified Data.IntMap as IMap

import System.Directory
import System.Environment
import System.Process
import System.Info
import System.IO
import System.FilePath ((</>))
import Options.Applicative
import Test.Tasty
import Test.Tasty.Golden
import Test.Tasty.Runners
import Test.Tasty.Options
import Test.Tasty.Ingredients.Rerun

import TestData

--------------------------------------------------------------------- [ Config ]

type Flags = [String]

-- Add arguments to calls of idris executable
idrisFlags :: Flags
idrisFlags = []

testDirectory :: String
testDirectory = "test"

-------------------------------------------------------------------- [ Options ]

-- The `--node` option makes idris use the node code generator
-- As a consequence, incompatible tests are removed

newtype NodeOpt = NodeOpt Bool deriving (Eq, Ord, Typeable)

nodeArg = "node"
nodeHelp = "Performs the tests with the node code generator"
instance IsOption NodeOpt where
  defaultValue = NodeOpt False
  parseValue = fmap NodeOpt . safeRead
  optionName = return nodeArg
  optionHelp = return nodeHelp
  optionCLParser = NodeOpt <$> switch (long nodeArg <> help nodeHelp)

ingredients :: [Ingredient]
ingredients = defaultIngredients ++
              [rerunningTests [consoleTestReporter],
               includingOptions [Option (Proxy :: Proxy NodeOpt)] ]

----------------------------------------------------------------------- [ Core ]

-- Compare a given file contents against the golden file contents
-- A ripoff of goldenVsFile from Tasty.Golden
test :: String -> String -> IO () -> TestTree
test testName path = goldenVsFileDiff testName diff ref output
  where
    ref = path </> "expected"
    output = path </> "output"
    diff ref new = ["diff", "--strip-trailing-cr", "-u", new, ref]

-- Should always output a 3-charater string from a postive Int
indexToString :: Int -> String
indexToString index = let str = show index in
                          replicate (3 - length str) '0' ++ str

-- Turns the collection of TestFamily into actual tests usable by Tasty
mkGoldenTests :: [TestFamily] -> Flags -> TestTree
mkGoldenTests testFamilies flags =
  testGroup "Regression and feature tests"
            (fmap mkTestFamily testFamilies)
    where
      mkTestFamily (TestFamily id name tests) =
        testGroup name (fmap (mkTest id) (IMap.keys tests))
      mkTest id index =
        let testname = id ++ indexToString index
            path = testDirectory </> testname
         in
          test testname path (runTest path flags)

-- Runs a test script
-- "bash" needed because Haskell has cmd as the default shell on windows, and
-- we also want to run the process with another current directory, so we get
-- this thing.
runTest :: String -> Flags -> IO ()
runTest path flags = do
  let run = (proc "bash" ("run" : flags)) {cwd = Just path,
                                           std_out = CreatePipe}
  (_, output, _) <- readCreateProcessWithExitCode run ""
  writeFile (path </> "output") (normalise output)
    where
      -- Normalise paths e.g. ".\foo.idr" to "./foo.idr".
      normalise ('.' : '\\' : c : xs) | isLetter c  = '.' : '/' : c : normalise xs
      normalise (x : xs) = x : normalise xs
      normalise [] = []

main :: IO ()
main =
  defaultMainWithIngredients ingredients $
    askOption $ \(NodeOpt node) ->
      let (codegen, flags) = if node then (JS, ["--codegen", "node"])
                                     else (C , [])
       in
        mkGoldenTests (testFamiliesForCodegen codegen)
                    (flags ++ idrisFlags)
