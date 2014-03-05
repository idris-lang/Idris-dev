module Debug.Trace

||| Print a message for debugging purposes as a side effect
||| @ msg what to print
||| @ result the final result
trace : (msg : String) -> (result : a) -> a
trace x val = unsafePerformIO (do putStrLn x; return val)


