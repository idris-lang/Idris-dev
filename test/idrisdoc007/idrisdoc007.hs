-- Tests that documentation only is written when safe

import Pkg.Package

main :: IO ()
main = documentPkg "package.ipkg"