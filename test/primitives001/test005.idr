module Main

tstr : String
tstr = "abc123"

tlist : List Int
tlist = [1, 2, 3, 4, 5]

main : IO ()
main = do printLn (abs (-8))
          printLn (span isAlpha tstr)
          printLn (break isDigit tstr)
          printLn (span (\x => x < 3) tlist)
          printLn (break (\x => x > 2) tlist)
