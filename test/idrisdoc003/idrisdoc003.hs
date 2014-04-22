-- Tests that documentation is generated for data types

import System.Directory
import Pkg.Package

main :: IO ()
main = do
  documentPkg "test_datatypes.ipkg"
  (doesDirectoryExist "test_datatypes_doc") >>= print
  