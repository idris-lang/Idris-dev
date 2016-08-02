module NonLayout

{-
Haskell and Idris use indentation for grouping in the concrete syntax.
How this works is defined as an automatic translation to the equivalent
syntax using { ; and }, which you are free to use yourself.

In Idris specifically, if let or where is followed by { then indentation no
longer matters for the following definitions until a balanced } appears. To
put multiple declarations on one line within the { } you put semicolons between
them: one ; for let declarations and ;; for where declarations. Whether this
discrepancy is a bug I don't know.
-}

average : String -> Double
average str = answer where
  wordCount : String -> Nat
  wordCount str = length (words str)
  wordLengths : List String -> List Nat
  wordLengths strs = map length strs
  answer =
    let numWords = wordCount str in
    let totalLength = sum (wordLengths (words str)) in
    cast totalLength / cast numWords

average' : String -> Double
average' str = answer where {
  wordCount : String -> Nat ;; wordCount str = length (words str)
 wordLengths : List String -> List Nat ;; wordLengths strs = map length strs
  answer = let {
    numWords = wordCount str; totalLength = sum (wordLengths (words str))
  } in cast totalLength / cast numWords
}
