module Main where

import Control.Monad
import Data.Typeable
import Data.Proxy
import Data.List
import Data.Map.Strict as Map
import Data.IntSet as ISet
import Data.IntMap as IMap
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC

import System.Directory
import System.Environment
import System.Process
import System.Info
import System.IO
import System.FilePath ((</>))
import Options.Applicative
import Test.Tasty
import Test.Tasty.Golden
import Test.Tasty.Golden.Advanced
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
  optionCLParser = fmap NodeOpt $ switch (long nodeArg <> help nodeHelp)

ingredients :: [Ingredient]
ingredients = [rerunningTests [consoleTestReporter],
               includingOptions [Option (Proxy :: Proxy NodeOpt)] ]

----------------------------------------------------------------------- [ Core ]

-- Compare a given file contents against the golden file contents
-- A ripoff of goldenVsFile from Tasty.Golden
test :: String -> String -> IO () -> TestTree
test name path act =
  goldenTest name (readFile ref) (act >> readFile new) cmp upd
    where
      ref = path </> "expected"
      new = path </> "output"
      cmp x y = return $ if normalize x == normalize y then Nothing
                                   else Just $ printDiff (ref, x) (new, y)
      upd = writeFile ref
      -- just pretend that backslashes are slashes for comparison
      -- purposes to avoid path problems, so don't write any tests
      -- that depend on that distinction in other contexts.
      -- Also compare CRLF and LF as equal, fixes a weird corner case
      -- on Mac where basic010 and reg039 produces CRLF
      normalize [] = []
      normalize ('\r':'\n':xs) = '\n' : normalize xs
      normalize ('\\':'\\':xs) = '/' : normalize xs
      normalize ('\\':xs) = '/' : normalize xs
      normalize (x : xs) = x : normalize xs


-- Takes the filepath and content of `expected` and `output`
-- and formats an error message stating their difference
printDiff :: (String, String) -> (String, String) -> String
printDiff (ref, x) (new, y) =
  let printContent cnt =
        if Data.List.null cnt
           then " is empty...\n"
           else " is: \n" ++ unlines (fmap ((++) "  ") (lines cnt))
   in
     "Test mismatch!\n" ++
       "Golden file " ++ ref ++ printContent x ++
       "However, " ++ new ++ printContent y

-- Should always output a 3-charater string from a postive Int
indexToString :: Int -> String
indexToString index = let str = show index in
                          (replicate (3 - length str) '0') ++ str

-- Turns the collection of TestFamily into actual tests usable by Tasty
mkGoldenTests :: [TestFamily] -> Flags -> TestTree
mkGoldenTests testFamilies flags =
  testGroup "Regression and sanity tests"
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
  writeFile (path </> "output") output

main :: IO ()
main = do
  defaultMainWithIngredients ingredients $
    askOption $ \(NodeOpt node) ->
      let (codegen, flags) = if node then (JS, ["--codegen", "node"])
                                     else (C , [])
       in
        mkGoldenTests (testFamiliesForCodegen codegen)
                    (flags ++ idrisFlags)
