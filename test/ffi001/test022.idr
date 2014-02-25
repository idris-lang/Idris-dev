module Main

%dynamic "dummy", "libm", "msvcrt"

x : Float64
x = unsafePerformIO (mkForeign (FFun "sin" [FFloat64] FFloat64) 1.6)

main : IO ()
main = putStrLn (show x)
