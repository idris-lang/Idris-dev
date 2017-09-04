module Text.Lexer

%default total

||| A language of token recognisers.
||| @ consumes If `True`, this recogniser is guaranteed to consume at
|||            least one character of input when it succeeds.
export
data Recognise : (consumes : Bool) -> Type where
     Empty : Recognise False
     Fail : Recognise c
     Expect : Recognise c -> Recognise False
     Pred : (Char -> Bool) -> Recognise True
     SeqEat : Recognise True -> Inf (Recognise e) -> Recognise True
     SeqEmpty : Recognise e1 -> Recognise e2 -> Recognise (e1 || e2)
     Alt : Recognise e1 -> Recognise e2 -> Recognise (e1 && e2)

||| A token recogniser. Guaranteed to consume at least one character.
public export
Lexer : Type
Lexer = Recognise True

public export
inf : Bool -> Type -> Type
inf True t = Inf t
inf False t = t

||| Sequence two recognisers. If either consumes a character, the sequence
||| is guaranteed to consume a character.
export %inline
(<+>) : {c1 : Bool} ->
        Recognise c1 -> inf c1 (Recognise c2) -> Recognise (c1 || c2)
(<+>) {c1 = False} = SeqEmpty
(<+>) {c1 = True} = SeqEat

||| Alternative recognisers. If both consume, the combination is guaranteed
||| to consumer a character.
export
(<|>) : Recognise c1 -> Recognise c2 -> Recognise (c1 && c2)
(<|>) = Alt

||| A recogniser that always fails.
export
fail : Recognise c
fail = Fail

||| Positive lookahead. Never consumes input.
export
expect : Recognise c -> Recognise False
expect = Expect

||| Negative lookahead. Never consumes input.
export
reject : Recognise c -> Recognise False
reject Empty            = Fail
reject Fail             = Empty
reject (Expect x)       = reject x
reject (Pred f)         = Expect (Pred (not . f))
reject (SeqEat r1 r2)   = reject r1 <|> Expect (SeqEat r1 (reject r2))
reject (SeqEmpty r1 r2) = reject r1 <|> Expect (SeqEmpty r1 (reject r2))
reject (Alt r1 r2)      = reject r1 <+> reject r2

||| Recognise a specific character
export
is : Char -> Lexer
is x = Pred (==x)

||| Recognise anything but the given character
export
isNot : Char -> Lexer
isNot x = Pred (/=x)

||| Recognise a character case-insensitively
export
like : Char -> Lexer
like x = Pred (\y => toUpper x == toUpper y)

||| Recognise anything but the given character case-insensitively
export
notLike : Char -> Lexer
notLike x = Pred (\y => toUpper x /= toUpper y)

||| Recognise a specific string
export
exact : String -> Lexer
exact str with (unpack str)
  exact str | [] = Fail -- Not allowed, Lexer has to consume
  exact str | (x :: xs)
      = foldl SeqEmpty (is x) (map is xs)

||| Recognise a specific string case-insensitively
export
approx : String -> Lexer
approx str with (unpack str)
  approx str | [] = Fail -- Not allowed, Lexer has to consume
  approx str | (x :: xs)
      = foldl SeqEmpty (like x) (map like xs)

||| Recognise a lexer or recognise no input. This is not guaranteed
||| to consume input
export
opt : Lexer -> Recognise False
opt l = l <|> Empty

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
choice xs = foldr Alt Fail xs

||| Recognise many instances of `l` until an instance of `end` is
||| encountered.
|||
||| Useful for defining comments.
export
manyTill : (l : Lexer) -> (end : Lexer) -> Recognise False
manyTill l end = end <|> opt (l <+> manyTill l end)

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
atMost Z _     = Empty
atMost (S k) l = atMost k l <+> opt l

||| Recognise a sub-lexer repeated between `min` and `max` times. Fails
||| if the inputs are out of order. Consumes input unless min is zero.
export
between : (min : Nat) -> (max : Nat) -> (l : Lexer) -> Recognise (min > 0)
between Z max l           = atMost max l
between (S min) Z _       = Fail
between (S min) (S max) l = l <+> between min max l

||| Recognise exactly `count` repeated occurrences of a sub-lexer.
||| Consumes input unless count is zero.
export
exactly : (count : Nat) -> (l : Lexer) -> Recognise (count > 0)
exactly n l = between n n l

||| Recognise any character
export
any : Lexer
any = Pred (const True)

||| Recognise any character if the sub-lexer `l` fails.
export
non : (l : Lexer) -> Lexer
non l = reject l <+> any

||| Recognise no input (doesn't consume any input)
export
empty : Recognise False
empty = Empty

||| Recognise a character that matches a predicate
export
pred : (Char -> Bool) -> Lexer
pred = Pred

||| Recognise any of the characters in the given string
export
oneOf : String -> Lexer
oneOf cs = pred (\x => x `elem` unpack cs)

data StrLen : Type where
     MkStrLen : String -> Nat -> StrLen

getString : StrLen -> String
getString (MkStrLen str n) = str

strIndex : StrLen -> Nat -> Maybe Char
strIndex (MkStrLen str len) i
    = if i >= len then Nothing
                  else Just (assert_total (prim__strIndex str (cast i)))

mkStr : String -> StrLen
mkStr str = MkStrLen str (length str)

strTail : Nat -> StrLen -> StrLen
strTail start (MkStrLen str len)
    = MkStrLen (substr start len str) (minus len start)

-- If the string is recognised, returns the index at which the token
-- ends
scan : Recognise c -> Nat -> StrLen -> Maybe Nat
scan Empty idx str = pure idx
scan Fail idx str = Nothing
scan (Expect r) idx str
    = case scan r idx str of
           Just _  => pure idx
           Nothing => Nothing
scan (Pred f) idx str
    = do c <- strIndex str idx
         if f c
            then Just (idx + 1)
            else Nothing
scan (SeqEat r1 r2) idx str
    = do idx' <- scan r1 idx str
         -- TODO: Can we prove totality instead by showing idx has increased?
         assert_total (scan r2 idx' str)
scan (SeqEmpty r1 r2) idx str
    = do idx' <- scan r1 idx str
         scan r2 idx' str
scan (Alt r1 r2) idx str
    = case scan r1 idx str of
           Nothing => scan r2 idx str
           Just idx => Just idx

takeToken : Lexer -> StrLen -> Maybe (String, StrLen)
takeToken lex str
    = do i <- scan lex 0 str -- i must be > 0 if successful
         pure (substr 0 i (getString str), strTail i str)

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
hexDigit = digit <|> oneOf "abcdefABCDEF"

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
surround start end l = start <+> manyTill l end

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
hexLit = is '0' <+> oneOf "xX" <+> hexDigits

||| A mapping from lexers to the tokens they produce.
||| This is a list of pairs `(Lexer, String -> tokenType)`
||| For each Lexer in the list, if a substring in the input matches, run
||| the associated function to produce a token of type `tokenType`
public export
TokenMap : (tokenType : Type) -> Type
TokenMap tokenType = List (Lexer, String -> tokenType)

||| A token, and the line and column where it was in the input
public export
record TokenData a where
  constructor MkToken
  line : Int
  col : Int
  tok : a

fspanEnd : Nat -> (Char -> Bool) -> String -> (Nat, String)
fspanEnd k p "" = (k, "")
fspanEnd k p xxs
    = assert_total $
      let x = prim__strHead xxs
          xs = prim__strTail xxs in
          if p x then fspanEnd (S k) p xs
                 else (k, xxs)

-- Faster version of 'span' from the prelude (avoids unpacking)
export
fspan : (Char -> Bool) -> String -> (String, String)
fspan p xs
    = let (end, rest) = fspanEnd 0 p xs in
          (substr 0 end xs, rest)

tokenise : (line : Int) -> (col : Int) ->
           List (TokenData a) -> TokenMap a ->
           StrLen -> (List (TokenData a), (Int, Int, StrLen))
tokenise line col acc tmap str
    = case getFirstToken tmap str of
           Just (tok, line', col', rest) =>
           -- assert total because getFirstToken must consume something
                assert_total (tokenise line' col' (tok :: acc) tmap rest)
           Nothing => (reverse acc, (line, col, str))
  where
    countNLs : List Char -> Nat
    countNLs str = List.length (filter (== '\n') str)

    getCols : String -> Int -> Int
    getCols x c
         = case fspan (/= '\n') (reverse x) of
                (incol, "") => c + cast (length incol)
                (incol, _) => cast (length incol)

    getFirstToken : TokenMap a -> StrLen -> Maybe (TokenData a, Int, Int, StrLen)
    getFirstToken [] str = Nothing
    getFirstToken ((lex, fn) :: ts) str
        = case takeToken lex str of
               Just (tok, rest) => Just (MkToken line col (fn tok),
                                         line + cast (countNLs (unpack tok)),
                                         getCols tok col, rest)
               Nothing => getFirstToken ts str

||| Given a mapping from lexers to token generating functions (the
||| TokenMap a) and an input string, return a list of recognised tokens,
||| and the line, column, and remainder of the input at the first point in the
||| string where there are no recognised tokens.
export
lex : TokenMap a -> String -> (List (TokenData a), (Int, Int, String))
lex tmap str = let (ts, (l, c, str')) = tokenise 0 0 [] tmap (mkStr str) in
                   (ts, (l, c, getString str'))
