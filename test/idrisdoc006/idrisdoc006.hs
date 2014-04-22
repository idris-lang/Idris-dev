-- Tests that documentation properly is merged with existing

import System.Directory
import System.FilePath
import Pkg.Package

main :: IO ()
main = do
  documentPkg "package_a.ipkg"
  documentPkg "package_b.ipkg"
  (doesFileExist $ "test_merge_doc" </> "docs" </> "A.html") >>= print
  (doesFileExist $ "test_merge_doc" </> "docs" </> "B.html") >>= print
  (readFile $ "test_merge_doc" </> "IdrisDoc") >>= putStr
  