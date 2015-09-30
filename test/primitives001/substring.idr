-- This is a test of the substring primitive, both in the Idris
-- evaluator and in some backend. It attempts to exercise that
-- negative indices are equivalent to 0, that it works for mixed
-- single- and multi-byte characters, and that overshooting the end
-- doesn't break things.

-- Single byte test
foo : String
foo = "Hello! here's the thing"

-- The first sentence of the Chinese wikipedia article on Idris (to
-- get mixed single-and-multibyte chars)
firstSentence : String
firstSentence = "Idris 是一个通用的依赖类型纯函数式编程语言，其类型系统与 Agda 以及 Epigram 相似。"

emptyTest : prim__strSubstr 100000 14 Main.firstSentence = ""
emptyTest = Refl

multiTest : prim__strSubstr 10 5 Main.firstSentence = "用的依赖类"
multiTest = Refl

negative : prim__strSubstr (-10) 5 Main.firstSentence = "Idris"
negative = Refl

negativeEnd : prim__strSubstr 0 (-1) Main.firstSentence = ""
negativeEnd = Refl

negativeLength : prim__strSubstr 4 (-4) Main.firstSentence = ""
negativeLength = Refl

main : IO ()
main = do putStrLn $ prim__strSubstr 1 1004 foo
          printLn $ length $ prim__strSubstr 1 1000 foo
          printLn $ length $ prim__strSubstr 1000 2 firstSentence
          putStrLn $ prim__strSubstr 10 5 firstSentence
          putStrLn $ prim__strSubstr (-10) 5 firstSentence
          putStrLn $ "[" ++ prim__strSubstr 0 (-1) firstSentence ++ "]"
          -- Multi-byte dynamic string
          input <- getLine
          putStrLn $ prim__strSubstr 3 8 input
          putStrLn $ show (length (prim__strSubstr 3 8 input))
          putStrLn $ prim__strSubstr 3 8000 input
          putStrLn $ show (length (prim__strSubstr 3 8000 input))
          putStrLn $ prim__strSubstr (-13) 18 input
          putStrLn $ show (length (prim__strSubstr (-13) 18 input))
          putStrLn $ prim__strSubstr 4 (-4) input
          putStrLn $ show (length (prim__strSubstr 4 (-4) input))
          -- Single-byte dynamic string
          input <- getLine
          putStrLn $ prim__strSubstr 3 8 input
          putStrLn $ show (length (prim__strSubstr 3 8 input))
          putStrLn $ prim__strSubstr 3 8000 input
          putStrLn $ show (length (prim__strSubstr 3 8000 input))
          putStrLn $ prim__strSubstr (-13) 18 input
          putStrLn $ show (length (prim__strSubstr (-13) 18 input))
          putStrLn $ prim__strSubstr 4 (-4) input
          putStrLn $ show (length (prim__strSubstr 4 (-4) input))

