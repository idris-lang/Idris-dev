module Data.String.Extra

%access public export
%default total

infixl 5 +>
infixr 5 <+

||| Adds a character to the end of the specified string.
|||
||| ```idris example
||| strSnoc "AB" 'C'
||| ```
||| ```idris example
||| strSnoc "" 'A'
||| ```
strSnoc : String -> Char -> String
strSnoc s c = s ++ (singleton c)

||| Alias of `strSnoc`
|||
||| ```idris example
||| "AB" +> 'C'
||| ```
(+>) : String -> Char -> String
(+>) = strSnoc

||| Alias of `strCons`
|||
||| ```idris example
||| 'A' <+ "AB"
||| ```
(<+) : Char -> String -> String
(<+) = strCons

||| Take the first `n` characters from a string. Returns the whole string
||| if it's too short.
take : (n : Nat) -> (input : String) -> String
take n str = substr Z n str

||| Take the last `n` characters from a string. Returns the whole string
||| if it's too short.
takeLast : (n : Nat) -> (input : String) -> String
takeLast n str with (length str)
  takeLast n str | len with (isLTE n len)
    takeLast n str | len | Yes prf = substr (len - n) len str
    takeLast n str | len | No contra = str

||| Remove the first `n` characters from a string. Returns the empty string if
||| the input string is too short.
drop : (n : Nat) -> (input : String) -> String
drop n str = substr n (length str) str

||| Remove the last `n` characters from a string. Returns the empty string if
||| the input string is too short.
dropLast : (n : Nat) -> (input : String) -> String
dropLast n str = reverse (drop n (reverse str))

||| Remove the first and last `n` characters from a string. Returns the empty
||| string if the input string is too short.
shrink : (n : Nat) -> (input : String) -> String
shrink n str = dropLast n (drop n str)

||| Concatenate the strings from a `Foldable` containing strings, separated by
||| the given string.
join : (sep : String) -> Foldable t => (xs : t String) -> String
join sep xs = drop (length sep)
                   (foldl (\acc, x => acc ++ sep ++ x) "" xs)

||| Get a character from a string if the string is long enough.
index : (n : Nat) -> (input : String) -> Maybe Char
index n str with (unpack str)
  index n str | [] = Nothing
  index Z str | (x :: xs) = Just x
  index (S n) str | (x :: xs) = index n str | xs

||| Produce a string by repeating the character `c` `n` times.
replicate : (n : Nat) -> (c : Char) -> String
replicate n c = pack $ replicate n c

||| Indent a given string by `n` spaces.
indent : (n : Nat) -> String -> String
indent n x = replicate n ' ' ++ x

||| Indent each line of a given string by `n` spaces.
indentLines : (n : Nat) -> String -> String
indentLines n str = unlines $ map (indent n) $ lines str

