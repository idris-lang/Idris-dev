module Debug.Trace

trace : String -> a -> a
trace x val = unsafePerformIO (do putStrLn x; return val)


