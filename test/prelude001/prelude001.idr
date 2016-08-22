module Main

main : IO ()
main = do
  printLn $ lines "" == []
  printLn $ lines "\n" == [""]
  printLn $ lines "\n\n" == ["", ""]
  printLn $ lines "\n\n\n" == ["", "", ""]
  printLn $ lines "1\n2\n3" == ["1", "2", "3"]
  printLn $ lines "1\n2\n3\n" == ["1", "2", "3"]
  printLn $ unlines [] == ""
  printLn $ unlines ["1"] == "1\n"
  printLn $ unlines ["1", "2"] == "1\n2\n"
  printLn $ unlines ["1", "2", "3"] == "1\n2\n3\n"
