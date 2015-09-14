-- The JS backend doesn't do Unicode input and output properly, so the
-- test of it is placed separately here so we can disable it for that
-- backend. If this is fixed, please enable this test for JS.
main : IO ()
main = do input <- getLine
          putStrLn $ prim__strSubstr 3 8 input
          putStrLn $ prim__strSubstr 3 8000 input
          putStrLn $ prim__strSubstr (-13) 18 input
