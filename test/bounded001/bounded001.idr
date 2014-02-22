module Main

-- Test wraparound from upper bounds of Bits types
main : IO ()
main = do putStrLn (show $ the Bits16 maxBound)
          putStrLn (show $ the Bits16 maxBound + 1)
          putStrLn (show $ the Bits32 maxBound)
          putStrLn (show $ the Bits32 maxBound + 1)
          putStrLn (show $ the Bits64 maxBound)
          putStrLn (show $ the Bits64 maxBound + 1)
