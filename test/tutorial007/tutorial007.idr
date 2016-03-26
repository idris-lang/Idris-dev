module Main
import Providers

%language TypeProviders
%provide (szSizeT : NativeTypeSize) with getSizeOfSizeT

main : IO ()
main = do
  (Right expected) <- readFile "sizefromc.txt" | (Left err) => printLn err
  putStrLn $ if show szSizeT == expected
             then "Pass"
             else "Fail: \"" ++ show szSizeT ++ "\" /= \"" ++ expected ++ "\""
