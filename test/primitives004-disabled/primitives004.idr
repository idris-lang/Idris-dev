module Main

main : IO ()
main = do
  putStrLn . show $ uniformB8x16 3
  putStrLn . show $ uniformB16x8 3
  putStrLn . show $ uniformB32x4 3
  putStrLn . show $ uniformB64x2 3
