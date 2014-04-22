-- Tests that documentation for empty namespaces are not created

import Pkg.Package

main :: IO ()
main = documentPkg "test_empty.ipkg"