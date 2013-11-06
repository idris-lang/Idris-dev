module Main

%include C "test033.h"
%link C "test033.o"

testNull : Ptr -> IO Int
testNull p = mkForeign (FFun "testNull" [FPtr] FInt) p

main : IO ()
main = testNull null >>= (putStrLn . show)
