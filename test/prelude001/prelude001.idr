module Main

main : IO ()
main = do
  printLn $ lines "" == []
  -- `lines` seems to ignore too many trailing newlines.
  printLn $ lines "\n" == [] -- FIXME: Should be [""].
  printLn $ lines "\n\n" == [] -- FIXME: Should be ["", ""].
  printLn $ lines "\n\n\n" == [] -- FIXME: Should be ["", "", ""].
  printLn $ lines "1\n2\n3" == ["1", "2", "3"]
  printLn $ lines "1\n2\n3\n" == ["1", "2", "3"]
  printLn $ unlines [] == ""
  -- `unlines` works as advertised doesn't follow Haskell here.
  -- When files are written using unlines, vim complains of "noeoln".
  printLn $ unlines ["1"] == "1" -- FIXME: Should be "1\n"
  printLn $ unlines ["1", "2"] == "1\n2" -- FIXME: Should be "1\n2\n"
  printLn $ unlines ["1", "2", "3"] == "1\n2\n3" -- FIXME: Should be "1\n2\n3\n"
