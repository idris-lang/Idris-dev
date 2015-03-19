module Main

main : IO ()
main = printLn . map val . unpack $ "\x0a\x80\xC9\xFF\n3\n4"
  where
    -- make the values positive if the backend has signed chars
    val : Char -> Int
    val = flip mod 256 . (+256) . ord
