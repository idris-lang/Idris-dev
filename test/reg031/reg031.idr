module Main

main : IO ()
main = print . map ord . unpack $ "\x0a\x80\xC9\xFF\n3\n4"
