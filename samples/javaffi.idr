module Main

%include Java "com.google.common.math.IntMath"
%lib Java "com.google.guava:guava:14.0"

binom : Int -> Int -> IO Int
binom n k = mkForeign (FFun "IntMath.binomial" [FInt, FInt] FInt) n k

main : IO ()
main = do print "The number of possibilities in lotto is 49 choose 6:"
       	  res <- binom 49 6
       	  printLn res
