module Text.Lexer

import public Text.Lexer.Core

%default total

||| Recognise a specific character
export
is : Char -> Lexer
is x = pred (==x)

||| Recognise anything but the given character
export
isNot : Char -> Lexer
isNot x = pred (/=x)

||| Recognise a character case-insensitively
export
like : Char -> Lexer
like x = pred (\y => toUpper x == toUpper y)

||| Recognise anything but the given character case-insensitively
export
notLike : Char -> Lexer
notLike x = pred (\y => toUpper x /= toUpper y)

||| Recognise a specific string.
||| Fails if the string is empty.
exact : String -> Lexer
exact str = case map is (unpack str) of
                 [] => fail
                 (x :: xs) => concat (x :: xs)

||| Recognise a specific string (case-insensitive).
||| Fails if the string is empty.
approx : String -> Lexer
approx str = case map like (unpack str) of
                  [] => fail
                  (x :: xs) => concat (x :: xs)

||| Recognise a lexer or recognise no input. This is not guaranteed
||| to consume input
export
opt : Lexer -> Recognise False
opt l = l <|> empty

||| Recognise a sequence of at least one sub-lexers
export
some : Lexer -> Lexer
some l = l <+> opt (some l)

||| Recognise a sequence of at zero or more sub-lexers. This is not
||| guaranteed to consume input
export
many : Lexer -> Recognise False
many l = opt (some l)

||| Recognise the first matching lexer from a Foldable. Always consumes input
||| if one of the options succeeds. Fails if the foldable is empty.
export
choice : Foldable t => t Lexer -> Lexer
choice xs = foldr (<|>) fail xs

||| Repeat the sub-lexer `l` zero or more times until the lexer
||| `stopBefore` is encountered. `stopBefore` will not be consumed.
||| Not guaranteed to consume input.
export
manyUntil : (stopBefore : Recognise c) -> (l : Lexer) -> Recognise False
manyUntil stopBefore l = many (reject stopBefore <+> l)

||| Repeat the sub-lexer `l` zero or more times until the lexer
||| `stopAfter` is encountered, and consume it. Guaranteed to
||| consume if `stopAfter` consumes.
export
manyThen : (stopAfter : Recognise c) -> (l : Lexer) -> Recognise c
manyThen stopAfter l = manyUntil stopAfter l <+> stopAfter

||| Recognise many instances of `l` until an instance of `end` is
||| encountered.
|||
||| Useful for defining comments.
export
manyTill : (l : Lexer) -> (end : Lexer) -> Recognise False
manyTill l end = end <|> opt (l <+> manyTill l end)
%deprecate manyTill
    "Prefer `lineComment`, or `manyUntil`/`manyThen` (argument order is flipped)."

||| Recognise a sub-lexer at least `min` times. Consumes input unless
||| min is zero.
export
atLeast : (min : Nat) -> (l : Lexer) -> Recognise (min > 0)
atLeast Z l       = many l
atLeast (S min) l = l <+> atLeast min l

||| Recognise a sub-lexer at most `max` times. Not guaranteed to
||| consume input.
export
atMost : (max : Nat) -> (l : Lexer) -> Recognise False
atMost Z _     = empty
atMost (S k) l = atMost k l <+> opt l

||| Recognise a sub-lexer repeated between `min` and `max` times. Fails
||| if the inputs are out of order. Consumes input unless min is zero.
export
between : (min : Nat) -> (max : Nat) -> (l : Lexer) -> Recognise (min > 0)
between Z max l           = atMost max l
between (S min) Z _       = fail
between (S min) (S max) l = l <+> between min max l

||| Recognise exactly `count` repeated occurrences of a sub-lexer.
||| Consumes input unless count is zero.
export
exactly : (count : Nat) -> (l : Lexer) -> Recognise (count > 0)
exactly n l = between n n l

||| Recognise any character
export
any : Lexer
any = pred (const True)

||| Recognise any character if the sub-lexer `l` fails.
export
non : (l : Lexer) -> Lexer
non l = reject l <+> any

||| Recognise any of the characters in the given string
export
oneOf : String -> Lexer
oneOf cs = pred (\x => x `elem` unpack cs)

||| Recognise a character range [`a`-`b`]. Also works in reverse!
export
range : (start : Char) -> (end : Char) -> Lexer
range start end = pred (\x => (x >= min start end)
                           && (x <= max start end))

||| Recognise a single digit 0-9
export
digit : Lexer
digit = pred isDigit

||| Recognise one or more digits
export
digits : Lexer
digits = some digit

||| Recognise a single hexidecimal digit
export
hexDigit : Lexer
hexDigit = pred isHexDigit

||| Recognise one or more hexidecimal digits
export
hexDigits : Lexer
hexDigits = some hexDigit

||| Recognise a single alpha character
export
alpha : Lexer
alpha = pred isAlpha

||| Recognise one or more alpha characters
export
alphas : Lexer
alphas = some alpha

||| Recognise a lowercase alpha character
export
lower : Lexer
lower = pred isLower

||| Recognise one or more lowercase alpha characters
export
lowers : Lexer
lowers = some lower

||| Recognise an uppercase alpha character
export
upper : Lexer
upper = pred isUpper

||| Recognise one or more uppercase alpha characters
export
uppers : Lexer
uppers = some upper

||| Recognise an alphanumeric character
export
alphaNum : Lexer
alphaNum = pred isAlphaNum

||| Recognise one or more alphanumeric characters
export
alphaNums : Lexer
alphaNums = some alphaNum

||| Recognise a single whitespace character
export
space : Lexer
space = pred isSpace

||| Recognise one or more whitespace characters
export
spaces : Lexer
spaces = some space

||| Recognise a single newline sequence. Understands CRLF, CR, and LF
export
newline : Lexer
newline = let crlf = "\r\n" in
              exact crlf <|> oneOf crlf

||| Recognise one or more newline sequences. Understands CRLF, CR, and LF
export
newlines : Lexer
newlines = some newline

||| Recognise a single non-whitespace, non-alphanumeric character
export
symbol : Lexer
symbol = pred (\x => not (isSpace x || isAlphaNum x))

||| Recognise one or more non-whitespace, non-alphanumeric characters
export
symbols : Lexer
symbols = some symbol

||| Recognise zero or more occurrences of a sub-lexer between
||| delimiting lexers
export
surround : (start : Lexer) -> (end : Lexer) -> (l : Lexer) -> Lexer
surround start end l = start <+> manyThen end l

||| Recognise zero or more occurrences of a sub-lexer surrounded
||| by the same quote lexer on both sides (useful for strings)
export
quote : (q : Lexer) -> (l : Lexer) -> Lexer
quote q l = surround q q l

||| Recognise an escape character (often '\\') followed by a sub-lexer
export
escape : (esc : Char) -> Lexer -> Lexer
escape esc l = is esc <+> l

||| Recognise a string literal, including escaped characters.
||| (Note: doesn't yet handle escape sequences such as \123)
export
stringLit : Lexer
stringLit = quote (is '"') (escape '\\' any <|> any)

||| Recognise a character literal, including escaped characters.
||| (Note: doesn't yet handle escape sequences such as \123)
export
charLit : Lexer
charLit = let q = '\'' in
              is q <+> (escape '\\' any <|> isNot q) <+> is q

||| Recognise an integer literal (possibly with a '-' prefix)
export
intLit : Lexer
intLit = opt (is '-') <+> digits

||| Recognise a hexidecimal literal, prefixed by "0x" or "0X"
export
hexLit : Lexer
hexLit = approx "0x" <+> hexDigits

||| Recognise `start`, then recognise all input until a newline is encountered,
||| and consume the newline. Will succeed if end-of-input is encountered before
||| a newline.
export
lineComment : (start : Lexer) -> Lexer
lineComment start = start <+> manyUntil newline any <+> opt newline

||| Recognise all input between `start` and `end` lexers.
||| Supports balanced nesting.
|||
||| For block comments that don't support nesting (such as C-style comments),
||| use `surround`.
export
blockComment : (start : Lexer) -> (end : Lexer) -> Lexer
blockComment start end = start <+> middle <+> end
  where
    middle : Recognise False
    middle = manyUntil end (blockComment start end <|> any)
