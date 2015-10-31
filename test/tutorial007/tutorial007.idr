module Main
import Providers
%language TypeProviders
%provide (szSizeT : NativeTypeSize) with getSizeOfSizeT

main : IO ()
main = do
  putStr "sizeof(size_t): "
  putStrLn (show szSizeT)
