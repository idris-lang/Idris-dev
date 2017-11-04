module basic025

-- converting data from strings at runtime so as to prevent the
-- compiler of eliding the calls to atan2 via constant folding
input : List (String, String, String)
input = [
  ("atan2", " 1", " 1"),
  ("atan2", "-1", " 1"),
  ("atan2", " 1", "-1"),
  ("atan2", "-1", "-1"),
  ("atan2", " 0", " 1"),
  ("atan2", " 1", " 0")
]

round : Double -> Double
round x = let y = x * 1e10
              z = if y < 0 then (ceiling y) else (floor y)
          in z / 1e10

-- the input file is read at runtime so as to prevent the compiler of
-- eliding the calls to atan2 via constant folding
namespace Main
  main : IO ()
  main = traverse_ evalInput input
    where
      evalInput : (String, String, String) -> IO ()
      evalInput ("atan2", y, x) = printLn $ round $ atan2 (cast y) (cast x)
      evalInput _ = putStrLn $ "Could not eval line"
