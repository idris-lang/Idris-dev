module Main

main : IO ()
main = print . map ord . unpack $ "\x0a\x80\xC9\xFF"
