module Main

%flag C "-ggdb3 -O0 -Q"

isn : String -> IO Int
isn s = mkForeign (FFun "isNull" [FString] FInt ) s

prn : String -> IO ()
prn s = mkForeign (FFun "putStr" [FString] FUnit) s

main : IO ()
main = isn "\n" >>= print
