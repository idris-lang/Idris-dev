-- Tests that documentation is generated for functions

import System.Directory
import Pkg.Package

main :: IO ()
main = do
  documentPkg "test_functions.ipkg"
  (doesDirectoryExist "test_functions_doc") >>= print
  