module Debug.Trace

||| Print a message for debugging purposes as a side effect
||| @ msg what to print
||| @ result the final result
export
trace : (msg : String) -> (result : a) -> a
trace x val = unsafePerformIO {ffi=FFI_C} (do putStrLn x; pure val)


