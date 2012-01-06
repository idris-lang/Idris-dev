module main

tstr : String
tstr = "abc123"

tlist : List Int
tlist = [1, 2, 3, 4, 5]

main : IO ()
main = do { print (abs (-8))
            print (abs (S O)) 
            print (span isAlpha tstr)
            print (break isDigit tstr)
            print (span (\x => x < 3) tlist)
            print (break (\x => x > 2) tlist)
          }
