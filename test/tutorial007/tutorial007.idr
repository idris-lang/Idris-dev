module Main
import Providers
%language TypeProviders
%provide (szSizeT : NativeTypeSize) with getSizeOfSizeT

main : IO ()
main = do
  expected <- readFile "sizefromc.txt"
  putStrLn $ if show szSizeT == expected
             then "Pass"
             else "Fail: \"" ++ show szSizeT ++ "\" /= \"" ++ expected ++ "\""
