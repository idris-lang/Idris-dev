-- Tests that documentation is generated for type classes

import System.Directory
import Pkg.Package

main :: IO ()
main = do
  documentPkg "test_typeclasses.ipkg"
  (doesDirectoryExist "test_typeclasses_doc") >>= print
  