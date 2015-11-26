module Main

%dynamic "dummy", "libm", "msvcrt"

x : Double
x = unsafePerformIO (foreign FFI_C "sin" (Double -> IO Double) 1.6)

main : IO ()
main = putStrLn (show x)
