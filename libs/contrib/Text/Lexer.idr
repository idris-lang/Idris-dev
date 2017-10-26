module Text.Lexer

import public Text.Lexer.Core

%default total
%access export

||| Recognise a specific character
is : Char -> Lexer
is x = pred (==x)

||| Recognise anything but the given character
isNot : Char -> Lexer
isNot x = pred (/=x)

||| Recognise a character case-insensitively
like : Char -> Lexer
like x = pred (\y => toUpper x == toUpper y)

||| Recognise anything but the given character case-insensitively
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
opt : Lexer -> Recognise False
opt l = l <|> empty

||| Recognise a sequence of at least one sub-lexers
some : Lexer -> Lexer
some l = l <+> opt (some l)

||| Recognise a sequence of at zero or more sub-lexers. This is not
||| guaranteed to consume input
many : Lexer -> Recognise False
many l = opt (some l)

||| Recognise the first matching lexer from a Foldable. Always consumes input
||| if one of the options succeeds. Fails if the foldable is empty.
choice : Foldable t => t Lexer -> Lexer
choice xs = foldr (<|>) fail xs

||| Repeat the sub-lexer `l` zero or more times until the lexer
||| `stopBefore` is encountered. `stopBefore` will not be consumed.
||| Not guaranteed to consume input.
manyUntil : (stopBefore : Recognise c) -> (l : Lexer) -> Recognise False
manyUntil stopBefore l = many (reject stopBefore <+> l)

||| Repeat the sub-lexer `l` zero or more times until the lexer
||| `stopAfter` is encountered, and consume it. Guaranteed to
||| consume if `stopAfter` consumes.
manyThen : (stopAfter : Recognise c) -> (l : Lexer) -> Recognise c
manyThen stopAfter l = manyUntil stopAfter l <+> stopAfter

||| Recognise many instances of `l` until an instance of `end` is
||| encountered.
|||
||| Useful for defining comments.
manyTill : (l : Lexer) -> (end : Lexer) -> Recognise False
manyTill l end = end <|> opt (l <+> manyTill l end)
%deprecate manyTill
    "Prefer `lineComment`, or `manyUntil`/`manyThen` (argument order is flipped)."

||| Recognise a sub-lexer at least `min` times. Consumes input unless
||| min is zero.
atLeast : (min : Nat) -> (l : Lexer) -> Recognise (min > 0)
atLeast Z l       = many l
atLeast (S min) l = l <+> atLeast min l

||| Recognise a sub-lexer at most `max` times. Not guaranteed to
||| consume input.
atMost : (max : Nat) -> (l : Lexer) -> Recognise False
atMost Z _     = empty
atMost (S k) l = atMost k l <+> opt l

||| Recognise a sub-lexer repeated between `min` and `max` times. Fails
||| if the inputs are out of order. Consumes input unless min is zero.
between : (min : Nat) -> (max : Nat) -> (l : Lexer) -> Recognise (min > 0)
between Z max l           = atMost max l
between (S min) Z _       = fail
between (S min) (S max) l = l <+> between min max l

||| Recognise exactly `count` repeated occurrences of a sub-lexer.
||| Consumes input unless count is zero.
exactly : (count : Nat) -> (l : Lexer) -> Recognise (count > 0)
exactly n l = between n n l

||| Recognise any character
any : Lexer
any = pred (const True)

||| Recognise any character if the sub-lexer `l` fails.
non : (l : Lexer) -> Lexer
non l = reject l <+> any

||| Recognise any of the characters in the given string
oneOf : String -> Lexer
oneOf cs = pred (\x => x `elem` unpack cs)

||| Recognise a character range [`a`-`b`]. Also works in reverse!
range : (start : Char) -> (end : Char) -> Lexer
range start end = pred (\x => (x >= min start end)
                           && (x <= max start end))

||| Recognise a single digit 0-9
digit : Lexer
digit = pred isDigit

||| Recognise one or more digits
digits : Lexer
digits = some digit

||| Recognise a single hexidecimal digit
hexDigit : Lexer
hexDigit = pred isHexDigit

||| Recognise one or more hexidecimal digits
hexDigits : Lexer
hexDigits = some hexDigit

||| Recognise a single alpha character
alpha : Lexer
alpha = pred isAlpha

||| Recognise one or more alpha characters
alphas : Lexer
alphas = some alpha

||| Recognise a lowercase alpha character
lower : Lexer
lower = pred isLower

||| Recognise one or more lowercase alpha characters
lowers : Lexer
lowers = some lower

||| Recognise an uppercase alpha character
upper : Lexer
upper = pred isUpper

||| Recognise one or more uppercase alpha characters
uppers : Lexer
uppers = some upper

||| Recognise an alphanumeric character
alphaNum : Lexer
alphaNum = pred isAlphaNum

||| Recognise one or more alphanumeric characters
alphaNums : Lexer
alphaNums = some alphaNum

||| Recognise a single whitespace character
space : Lexer
space = pred isSpace

||| Recognise one or more whitespace characters
spaces : Lexer
spaces = some space

||| Recognise a single newline sequence. Understands CRLF, CR, and LF
newline : Lexer
newline = let crlf = "\r\n" in
              exact crlf <|> oneOf crlf

||| Recognise one or more newline sequences. Understands CRLF, CR, and LF
newlines : Lexer
newlines = some newline

||| Recognise a single non-whitespace, non-alphanumeric character
symbol : Lexer
symbol = pred (\x => not (isSpace x || isAlphaNum x))

||| Recognise one or more non-whitespace, non-alphanumeric characters
symbols : Lexer
symbols = some symbol

||| Recognise zero or more occurrences of a sub-lexer between
||| delimiting lexers
surround : (start : Lexer) -> (end : Lexer) -> (l : Lexer) -> Lexer
surround start end l = start <+> manyThen end l

||| Recognise zero or more occurrences of a sub-lexer surrounded
||| by the same quote lexer on both sides (useful for strings)
quote : (q : Lexer) -> (l : Lexer) -> Lexer
quote q l = surround q q l

||| Recognise an escape character (often '\\') followed by a sub-lexer
escape : (esc : Char) -> Lexer -> Lexer
escape esc l = is esc <+> l

||| Recognise a string literal, including escaped characters.
||| (Note: doesn't yet handle escape sequences such as \123)
stringLit : Lexer
stringLit = quote (is '"') (escape '\\' any <|> any)

||| Recognise a character literal, including escaped characters.
||| (Note: doesn't yet handle escape sequences such as \123)
charLit : Lexer
charLit = let q = '\'' in
              is q <+> (escape '\\' any <|> isNot q) <+> is q

||| Recognise an integer literal (possibly with a '-' prefix)
intLit : Lexer
intLit = opt (is '-') <+> digits

||| Recognise a hexidecimal literal, prefixed by "0x" or "0X"
hexLit : Lexer
hexLit = approx "0x" <+> hexDigits

||| Recognise `start`, then recognise all input until a newline is encountered,
||| and consume the newline. Will succeed if end-of-input is encountered before
||| a newline.
lineComment : (start : Lexer) -> Lexer
lineComment start = start <+> manyUntil newline any <+> opt newline

||| Recognise all input between `start` and `end` lexers.
||| Supports balanced nesting.
|||
||| For block comments that don't support nesting (such as C-style comments),
||| use `surround`.
blockComment : (start : Lexer) -> (end : Lexer) -> Lexer
blockComment start end = start <+> middle <+> end
  where
    middle : Recognise False
    middle = manyUntil end (blockComment start end <|> any)
