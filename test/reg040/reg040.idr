-- The regression that this tests for is defunct unsafePerformIO

io : IO Int
io = pure 42

main : IO ()
main = printLn $ unsafePerformIO io
