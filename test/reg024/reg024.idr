module Main

data Format = End | FInt Format | FStr Format | FChar Char Format

fromList : List Char -> Format
fromList Nil                = End
fromList ('%' :: 'd' :: cs) = FInt    (fromList cs)
fromList ('%' :: 's' :: cs) = FStr (fromList cs)
fromList (c :: cs)          = FChar c (fromList cs)

PrintfType : Format -> Type
PrintfType End            = String
PrintfType (FInt rest)    = Int -> PrintfType rest
PrintfType (FStr rest) = String -> PrintfType rest
PrintfType (FChar c rest) = PrintfType rest

printf : (fmt: String) -> PrintfType (fromList $ unpack fmt)
printf fmt = printFormat (fromList $ unpack fmt) where
 printFormat : (fmt: Format) -> PrintfType fmt
 printFormat fmt = rec fmt "" where
   rec : (f: Format) -> String -> PrintfType f
   rec End acc            = acc
   rec (FInt rest) acc    = \i: Int => rec rest (acc ++ (show i))
   rec (FStr rest) acc = \s: String => rec rest (acc ++ s)
   rec (FChar c rest) acc = rec rest (acc ++ (strCons c ""))

test : String
test = printf "The %s is %d" "answer" 42

main : IO ()
main = putStrLn test
