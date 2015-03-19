-- The regression that this tests for is defunct unsafePerformIO

io : IO Int
io = return 42

main : IO ()
main = printLn $ unsafePerformIO io
