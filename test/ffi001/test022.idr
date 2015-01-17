module Main

%dynamic "dummy", "libm", "msvcrt"

x : Float
x = unsafePerformIO (foreign FFI_C "sin" (Float -> IO Float) 1.6)

main : IO ()
main = putStrLn (show x)
