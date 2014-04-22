-- Tests that references to other namespaces are traced

import System.Directory
import System.FilePath
import Pkg.Package

main :: IO ()
main = do
  documentPkg "test_tracing.ipkg"
  let docs = "test_tracing_doc" </> "docs"
  (doesFileExist $ docs </> "TestTracing.html") >>= print
  (doesFileExist $ docs </> "Prelude.Bool.html") >>= print